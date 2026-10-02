import Blanc.Lift.UniswapV2Pair.TransferCore
import Blanc.Lift.InvWalkProvenance

/-! The actual LP mint stores supply before reading and crediting the recipient. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def lpMintMemory (M : Mem) (toWord value : B256) : Mem :=
  ((M.write 0 toWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes).write 128 value.toBytes

def lpMintCreditBase (sevm : Sevm) (b : Devm) (toWord value credited : B256) : Devm :=
  (afterSstore sevm b (transferBalanceSlot toWord.toAdr) credited).addLog
    ⟨sevm.currentTarget, [transferTopic, 0, toWord.toAdr.toB256], value.toBytes⟩

def lpMintCreditPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (toWord value credited : B256) (G : Nat) : Devm :=
  St (lpMintCreditBase sevm b toWord value credited) R (lpMintMemory M toWord value) G

theorem lpMintScratch_ptr {M : Mem} (mem : PtrMem 128 192 M) (toWord : B256) :
    PtrMem 128 192 ((M.write 0 toWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes) := by
  have a := mem.write 0 toWord.toAdr.toB256 (Or.inl (by decide))
  rw [show memExtSize 192 0 32 = 192 from by decide] at a
  have b := a.write 32 1 (Or.inl (by decide))
  rw [show memExtSize 192 32 32 = 192 from by decide] at b
  exact b

theorem lpMintMemory_ptr {M : Mem} (mem : PtrMem 128 192 M) (toWord value : B256) :
    PtrMem 128 192 (lpMintMemory M toWord value) := by
  have h := (lpMintScratch_ptr mem toWord).write 128 value (Or.inr (by decide))
  rw [show memExtSize 192 128 32 = 192 from by decide] at h
  exact h

/-- Literal recipient SSTORE, Transfer(0,to,value), and internal return. -/
theorem lpMint_credit_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {toWord value credited ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (cost : c = sstoreCost sevm b (transferBalanceSlot toWord.toAdr) credited)
    (sentry : gCallStipend < G + c + 1828) (nonstatic : sevm.isStatic = false)
    (room : R.length ≤ 1014) :
    SFunc.RunExact fs sevm (St b (credited :: value :: toWord :: ρ :: R) M (G + c + 1925))
      t_2915_c62 (.returned (lpMintCreditPost sevm b R M toWord value credited G)) := by
  have m0 := mem.write 0 toWord.toAdr.toB256 (Or.inl (by decide))
  rw [show memExtSize 192 0 32 = 192 from by decide] at m0
  have m1 := lpMintScratch_ptr mem toWord
  have m2 := lpMintMemory_ptr mem toWord value
  have s1 : ((M.write 0 toWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes).size = 192 := m1.size
  have s2 : (((M.write 0 toWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes).write 128 value.toBytes).size = 192 := m2.size
  unfold t_2915_c62
  refine rx_dest ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := toWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word toWord)
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
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  simp only [show (0 : B256).toNat = 0 from rfl, show (32 : B256).toNat = 32 from rfl]
  have gh : G + c + 1879 = (G + c + 1837) + 42 := by omega
  rw [gh]
  refine rx_keccak (v := transferBalanceSlot toWord.toAdr) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 toWord.toAdr.toB256 1)
  refine rx_swap (n := 4) rfl ?_
  dsimp only [List.set]
  refine rx_swap1 ?_
  refine rx_swap (n := 4) rfl ?_
  dsimp only [List.set]
  have gs : G + c + 1828 = (G + 1828) + c := by omega
  rw [gs]
  refine rx_sstoreC fork cost (by omega) nonstatic ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ m1.word (m1.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq s1]; decide
  simp only [show (128 : B256).toNat = 128 from rfl]
  refine rx_swap4 ?_
  refine rx_mload (c := 3) ?_ m2.word (m2.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s2]; decide
  refine rx_swap3 ?_
  refine rx_swap4 ?_
  refine rx_swap2 ?_
  refine rx_swap3 ?_
  refine rx_push (w := transferTopic) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  have gl : G + 1768 = (G + 12) + 1756 := by omega
  rw [gl]
  refine rx_log3 (data := value.toBytes) nonstatic ?_ ?_ (m2.read_self (by decide)) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq s2]; decide
  · exact Mem.read_write_word_of_wf m1.wf 128 value
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

/-- A successful literal continuation determines the complete recipient-store/log image. -/
theorem lpMint_credit_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {toWord value credited ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run fs sevm (St b (credited :: value :: toWord :: ρ :: R) M G) t_2915_c62 o) :
    sevm.isStatic = false ∧
      ∃ residual, o = .returned (lpMintCreditPost sevm b R M toWord value credited residual) := by
  have m1 := lpMintScratch_ptr mem toWord
  have m2 := lpMintMemory_ptr mem toWord value
  have hash := congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 toWord.toAdr.toB256 1)
  dsimp only [lpMintMemory] at m2
  have ptr1 := m1.word
  have ptr2 := m2.word
  dsimp only [memWord] at ptr1 ptr2
  have h := run.cut
  unfold t_2915_c62 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := toWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word toWord) (ri_and hd)
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
  simp only [List.set] at h
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
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 192), hash] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl, m1.read_self (by decide : 64 + 32 ≤ 192), ptr1] at hd
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
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl, m2.read_self (by decide : 64 + 32 ≤ 192), ptr2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xdd, 0xf2, 0x52, 0xad, 0x1b, 0xe2, 0xc8, 0x9b, 0x69, 0xc2, 0xb0, 0x68, 0xfc, 0x37, 0x8d, 0xaa, 0x95, 0x2b, 0xa7, 0xf1, 0x63, 0xc4, 0xa1, 0x16, 0x28, 0xf5, 0x5a, 0x4d, 0xf5, 0x23, 0xb3, 0xef] = (transferTopic : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_sub hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 32) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_log3 hd
  simp only [show (128 : B256).toNat = 128 from rfl, show (32 : B256).toNat = 32 from rfl,
    m2.read_self (by decide : 128 + 32 ≤ 192), Mem.read_write_word_of_wf m1.wf 128 value] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨residual, eq⟩ := ric_ret h
  exact ⟨nonstatic, residual, Seg.done.inj eq⟩

def lpMintSupplyBase (sevm : Sevm) (b : Devm) (supply : B256) : Devm :=
  afterSstore sevm b 0 supply

def lpMintRecipientWord (sevm : Sevm) (b : Devm) (toWord supply : B256) : B256 :=
  (lpMintSupplyBase sevm b supply).getStorVal sevm.currentTarget (transferBalanceSlot toWord.toAdr)

def lpMintSupplyPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (toWord value supply : B256) (G : Nat) : Devm :=
  lpMintCreditPost sevm
    (afterSload sevm (lpMintSupplyBase sevm b supply) (transferBalanceSlot toWord.toAdr)) R
    ((M.write 0 toWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes)
    toWord value (lpMintRecipientWord sevm b toWord supply + value) G

/-- The literal supply store precedes the recipient load, including raw alias at slot zero. -/
theorem lpMint_supply_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G supplyCost loadCost creditCost : Nat} {toWord value supply ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (supplyEq : supplyCost = sstoreCost sevm b 0 supply)
    (loadEq : loadCost = sloadCost sevm (lpMintSupplyBase sevm b supply) (transferBalanceSlot toWord.toAdr))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (lpMintSupplyBase sevm b supply) (transferBalanceSlot toWord.toAdr))
      (transferBalanceSlot toWord.toAdr) (lpMintRecipientWord sevm b toWord supply + value))
    (supplySentry : gCallStipend < G + supplyCost + loadCost + creditCost + 2077)
    (creditSentry : gCallStipend < G + creditCost + 1828)
    (nonstatic : sevm.isStatic = false)
    (nowrap : (lpMintRecipientWord sevm b toWord supply).toNat + value.toNat < 2 ^ 256)
    (room : R.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (supply :: value :: toWord :: ρ :: R)
      M (G + supplyCost + loadCost + creditCost + 2087)) t_28dd_c62
      (.returned (lpMintSupplyPost sevm b R M toWord value supply G)) := by
  have m0 := mem.write 0 toWord.toAdr.toB256 (Or.inl (by decide))
  rw [show memExtSize 192 0 32 = 192 from by decide] at m0
  have m1 := lpMintScratch_ptr mem toWord
  have s1 : ((M.write 0 toWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes).size = 192 := m1.size
  unfold t_28dd_c62
  refine rx_dest ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  have gs : G + supplyCost + loadCost + creditCost + 2077 =
    (G + loadCost + creditCost + 2077) + supplyCost := by omega
  rw [gs]
  refine rx_sstoreC fork supplyEq (by omega) nonstatic ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := toWord.toAdr.toB256) (by rw [B256.and_comm]; exact ff20_and_word toWord)
    (by simp only [List.length_cons]; omega) ?_
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
  have gh : G + loadCost + creditCost + 2047 = (G + loadCost + creditCost + 2005) + 42 := by omega
  rw [gh]
  refine rx_keccak (v := transferBalanceSlot toWord.toAdr) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 toWord.toAdr.toB256 1)
  have gl : G + loadCost + creditCost + 2005 = (G + creditCost + 2005) + loadCost := by omega
  rw [gl]
  refine rx_sload_selC fork loadEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x2915) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x2abc) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0x2abc) (by decide) (by simp only [List.length_cons]; omega) ?_
  have gc : G + creditCost + 1987 = ((G + creditCost + 1925) + 54) + 8 := by omega
  rw [gc]
  refine rx_callRet (g := t_2abc_c72) rfl
    (add72_exact nowrap (by simp only [List.length_cons]; omega)) ?_
  exact lpMint_credit_exact fork m1 creditEq creditSentry nonstatic room

/-- Inverse derives non-static execution and recipient no-wrap after the supply store. -/
theorem lpMint_supply_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {toWord value supply ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm (St b (supply :: value :: toWord :: ρ :: R) M G) t_28dd_c62 o) :
    sevm.isStatic = false ∧
      (lpMintRecipientWord sevm b toWord supply).toNat + value.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (lpMintSupplyPost sevm b R M toWord value supply residual) := by
  have m1 := lpMintScratch_ptr mem toWord
  have hash := congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 toWord.toAdr.toB256 1)
  have h := run.cut
  unfold t_28dd_c62 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := toWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word toWord) (ri_and hd)
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
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show (0 : B256).toNat = 0 from rfl, show (64 : B256).toNat = 64 from rfl,
    m1.read_self (by decide : 0 + 64 ≤ 192), hash] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x29, 0x15] = (10517 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
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
    obtain ⟨_, residual, result⟩ := lpMint_credit_inv fork m1 tail.uncut
    exact ⟨nonstatic, nowrap, residual, result⟩
  · obtain ⟨_, _, eq⟩ := add72_inv checked
    cases eq

def lpMintSupplyWord (sevm : Sevm) (b : Devm) : B256 := b.getStorVal sevm.currentTarget 0

def lpMintPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (toWord value : B256) (G : Nat) : Devm :=
  lpMintSupplyPost sevm (afterSload sevm b 0) R M toWord value (lpMintSupplyWord sevm b + value) G

/-- Entry62 follows both checked additions and all four actual storage charges. -/
theorem lpMint62_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G sourceCost supplyCost loadCost creditCost : Nat} {toWord value ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (sourceEq : sourceCost = sloadCost sevm b 0)
    (supplyEq : supplyCost = sstoreCost sevm (afterSload sevm b 0) 0 (lpMintSupplyWord sevm b + value))
    (loadEq : loadCost = sloadCost sevm
      (lpMintSupplyBase sevm (afterSload sevm b 0) (lpMintSupplyWord sevm b + value))
      (transferBalanceSlot toWord.toAdr))
    (creditEq : creditCost = sstoreCost sevm
      (afterSload sevm (lpMintSupplyBase sevm (afterSload sevm b 0) (lpMintSupplyWord sevm b + value))
        (transferBalanceSlot toWord.toAdr)) (transferBalanceSlot toWord.toAdr)
      (lpMintRecipientWord sevm (afterSload sevm b 0) toWord (lpMintSupplyWord sevm b + value) + value))
    (supplySentry : gCallStipend < G + supplyCost + loadCost + creditCost + 2077)
    (creditSentry : gCallStipend < G + creditCost + 1828)
    (nonstatic : sevm.isStatic = false)
    (supplyNoWrap : (lpMintSupplyWord sevm b).toNat + value.toNat < 2 ^ 256)
    (recipientNoWrap : (lpMintRecipientWord sevm (afterSload sevm b 0) toWord
      (lpMintSupplyWord sevm b + value)).toNat + value.toNat < 2 ^ 256)
    (room : R.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (value :: toWord :: ρ :: R)
      M (G + sourceCost + supplyCost + loadCost + creditCost + 2171)) t_28ca_c62
      (.returned (lpMintPost sevm b R M toWord value G)) := by
  unfold t_28ca_c62
  refine rx_dest ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  have gs : G + sourceCost + supplyCost + loadCost + creditCost + 2167 =
    (G + supplyCost + loadCost + creditCost + 2167) + sourceCost := by omega
  rw [gs]
  refine rx_sload_selC fork sourceEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x28dd) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x2abc) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0x2abc) (by decide) (by simp only [List.length_cons]; omega) ?_
  have gc : G + supplyCost + loadCost + creditCost + 2149 =
    ((G + supplyCost + loadCost + creditCost + 2087) + 54) + 8 := by omega
  rw [gc]
  refine rx_callRet (g := t_2abc_c72) rfl
    (add72_exact supplyNoWrap (by simp only [List.length_cons]; omega)) ?_
  exact lpMint_supply_exact fork mem supplyEq loadEq creditEq supplySentry creditSentry
    nonstatic recipientNoWrap room

/-- No source endpoint is assumed: the successful bytecode run derives both guards and full post. -/
theorem lpMint62_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {toWord value ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm (St b (value :: toWord :: ρ :: R) M G) t_28ca_c62 o) :
    (lpMintSupplyWord sevm b).toNat + value.toNat < 2 ^ 256 ∧ sevm.isStatic = false ∧
      (lpMintRecipientWord sevm (afterSload sevm b 0) toWord
        (lpMintSupplyWord sevm b + value)).toNat + value.toNat < 2 ^ 256 ∧
      ∃ residual, o = .returned (lpMintPost sevm b R M toWord value residual) := by
  have h := run.cut
  unfold t_28ca_c62 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x28, 0xdd] = (0x28dd : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff] = (0xffffffff : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x2a, 0xbc] = (0x2abc : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0x2abc) (by decide) (ri_and hd)
  obtain ⟨_, call⟩ := ric_call (g := t_2abc_c72) rfl h
  rcases call with ⟨d, checked, tail⟩ | ⟨d, checked, _⟩
  · obtain ⟨supplyNoWrap, _, eq⟩ := add72_inv checked
    cases eq
    obtain ⟨nonstatic, recipientNoWrap, residual, result⟩ := lpMint_supply_inv fork mem tail.uncut
    exact ⟨supplyNoWrap, nonstatic, recipientNoWrap, residual, result⟩
  · obtain ⟨_, _, eq⟩ := add72_inv checked
    cases eq

def lpMintAccepts (sevm : Sevm) (b : Devm) (toWord value : B256) : Prop :=
  (lpMintSupplyWord sevm b).toNat + value.toNat < 2 ^ 256 ∧ sevm.isStatic = false ∧
    (lpMintRecipientWord sevm (afterSload sevm b 0) toWord
      (lpMintSupplyWord sevm b + value)).toNat + value.toNat < 2 ^ 256

/-- Actual fee caller retains its instruction relation and literal continuation. -/
theorem lpMint_fee_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {L D N bWord aWord KWord w feeOn r1 r0 feeρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (L :: D :: N :: bWord :: aWord :: KWord :: w :: feeOn :: r1 :: r0 :: feeρ :: R) M G) t_284f_c68 r) :
    ∃ mintGas residual,
      SFunc.RunP P cert.prog sevm (St b (L :: w :: 0x2858 :: L :: D :: N :: bWord :: aWord :: KWord :: w :: feeOn :: r1 :: r0 :: feeρ :: R) M mintGas)
        t_28ca_c62 (.returned (lpMintPost sevm b (L :: D :: N :: bWord :: aWord :: KWord :: w :: feeOn :: r1 :: r0 :: feeρ :: R) M w L residual)) ∧
      lpMintAccepts sevm b w L ∧
      SFunc.RunCutP P cert.prog sevm C (lpMintPost sevm b (L :: D :: N :: bWord :: aWord :: KWord :: w :: feeOn :: r1 :: r0 :: feeρ :: R) M w L residual) t_2858_c68 r := by
  have h := run
  unfold t_284f_c68 at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x28, 0x58] = (10328 : B256) from by decide] at hd'
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x28, 0xca] = (10442 : B256) from by decide] at hd'
  subst d
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_28ca_c62 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨supplyGuard, nonstatic, recipientGuard, residual, result⟩ := lpMint62_inv fork mem (callee.mono project)
    cases result
    exact ⟨_, residual, callee, ⟨supplyGuard, nonstatic, recipientGuard⟩, continuation⟩
  | callHalt d lookup pop callee =>
    change some t_28ca_c62 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, _, _, _, result⟩ := lpMint62_inv fork mem (callee.mono project)
    cases result

/-- Actual minimum caller retains its instruction relation and literal continuation. -/
theorem lpMint_minimum_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {liquidity supplyWord f amount1 amount0 b1 b0 r1 r0 oldLiquidity toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (liquidity :: supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: oldLiquidity :: toWord :: extρ :: R) M G) t_125c_c41 r) :
    ∃ mintGas residual,
      SFunc.RunP P cert.prog sevm (St b (1000 :: 0 :: 0x126b :: supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: extρ :: R) M mintGas)
        t_28ca_c62 (.returned (lpMintPost sevm b (supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: extρ :: R) M 0 1000 residual)) ∧
      lpMintAccepts sevm b 0 1000 ∧
      SFunc.RunCutP P cert.prog sevm C (lpMintPost sevm b (supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: extρ :: R) M 0 1000 residual) t_126b_c41 r := by
  have h := run
  unfold t_125c_c41 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_swap rfl (project hd)
  subst d
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_pop (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x12, 0x6b] = (4715 : B256) from by decide] at hd'
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from by decide] at hd'
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x03, 0xe8] = (1000 : B256) from by decide] at hd'
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x28, 0xca] = (10442 : B256) from by decide] at hd'
  subst d
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_28ca_c62 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨supplyGuard, nonstatic, recipientGuard, residual, result⟩ := lpMint62_inv fork mem (callee.mono project)
    cases result
    exact ⟨_, residual, callee, ⟨supplyGuard, nonstatic, recipientGuard⟩, continuation⟩
  | callHalt d lookup pop callee =>
    change some t_28ca_c62 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, _, _, _, result⟩ := lpMint62_inv fork mem (callee.mono project)
    cases result

/-- Actual recipient caller retains its instruction relation and literal continuation. -/
theorem lpMint_recipient_caller_inv {P : Sevm → Devm → Ninst → Devm → Prop}
    {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {supplyWord f amount1 amount0 b1 b0 r1 r0 liquidity toWord extρ : B256}
    (project : ∀ {e d n d'}, P e d n d' → Ninst.Run e d n d')
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.RunCutP P cert.prog sevm C (St b (supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: extρ :: R) M G) t_1326_c11 r) :
    ∃ mintGas residual,
      SFunc.RunP P cert.prog sevm (St b (liquidity :: toWord :: 0x1330 :: supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: extρ :: R) M mintGas)
        t_28ca_c62 (.returned (lpMintPost sevm b (supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: extρ :: R) M toWord liquidity residual)) ∧
      lpMintAccepts sevm b toWord liquidity ∧
      SFunc.RunCutP P cert.prog sevm C (lpMintPost sevm b (supplyWord :: f :: amount1 :: amount0 :: b1 :: b0 :: r1 :: r0 :: liquidity :: toWord :: extρ :: R) M toWord liquidity residual) t_1330_c11 r := by
  have h := run
  unfold t_1326_c11 at h
  obtain ⟨_, h⟩ := ric_destP h
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x13, 0x30] = (4912 : B256) from by decide] at hd'
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, eq⟩ := ri_dup rfl (project hd)
  subst d
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, hd'⟩ := ri_push (project hd)
  simp only [show Bytes.toB256 [0x28, 0xca] = (10442 : B256) from by decide] at hd'
  subst d
  cases h with
  | callRet d lookup pop callee continuation =>
    change some t_28ca_c62 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨supplyGuard, nonstatic, recipientGuard, residual, result⟩ := lpMint62_inv fork mem (callee.mono project)
    cases result
    exact ⟨_, residual, callee, ⟨supplyGuard, nonstatic, recipientGuard⟩, continuation⟩
  | callHalt d lookup pop callee =>
    change some t_28ca_c62 = _ at lookup
    cases lookup
    obtain ⟨_, eq⟩ := St.of_pop1 pop
    rw [eq] at callee
    obtain ⟨_, _, _, _, result⟩ := lpMint62_inv fork mem (callee.mono project)
    cases result

end Blanc.Lift.UniswapV2Pair
