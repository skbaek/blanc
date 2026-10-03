import Blanc.Lift.UniswapV2Pair.LPMintCore
import Blanc.Lift.UniswapV2Pair.WriterArithmetic

/-! Literal LP burn 63: balance debit precedes total-supply debit. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def lpBurnSupplyBase (sevm : Sevm) (b : Devm) (fromWord value supply : B256) : Devm :=
  (afterSstore sevm b 0 supply).addLog
    ⟨sevm.currentTarget, [transferTopic, fromWord.toAdr.toB256, 0], value.toBytes⟩

def lpBurnSupplyPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (fromWord value supply : B256) (G : Nat) : Devm :=
  St (lpBurnSupplyBase sevm b fromWord value supply) R (M.write 128 value.toBytes) G

/-- The actual second store and Transfer(from,0,value) tail of LP burn 63. -/
theorem lpBurn_supply_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {fromWord value supply ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (cost : c = sstoreCost sevm b 0 supply)
    (sentry : gCallStipend < G + c + 1831) (nonstatic : sevm.isStatic = false)
    (room : R.length ≤ 1014) :
    SFunc.RunExact fs sevm (St b (supply :: value :: fromWord :: ρ :: R) M (G + c + 1841))
      t_2a02_c63 (.returned (lpBurnSupplyPost sevm b R M fromWord value supply G)) := by
  have m1 := mem.write 128 value (Or.inr (by decide))
  rw [show memExtSize 192 128 32 = 192 from by decide] at m1
  unfold t_2a02_c63
  refine rx_dest ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  have gs : G + c + 1831 = (G + 1831) + c := by omega
  rw [gs]
  refine rx_sstoreC fork cost (by omega) nonstatic ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  simp only [show (128 : B256).toNat = 128 from rfl]
  refine rx_swap1 ?_
  refine rx_mload (c := 3) ?_ m1.word (m1.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m1.size]; decide
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := fromWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word fromWord)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_push (w := transferTopic) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap2 ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  have gl : G + 1768 = (G + 12) + 1756 := by omega
  rw [gl]
  refine rx_log3 (data := value.toBytes) nonstatic ?_ ?_ (m1.read_self (by decide)) ?_
  · rw [St.extCost_eq m1.size]; decide
  · exact Mem.read_write_word_of_wf mem.wf 128 value
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

/-- Successful LP burn return derives the supply write and exact raw Transfer log. -/
theorem lpBurn_supply_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {fromWord value supply ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run fs sevm (St b (supply :: value :: fromWord :: ρ :: R) M G) t_2a02_c63 o) :
    sevm.isStatic = false ∧
      ∃ residual, o = .returned (lpBurnSupplyPost sevm b R M fromWord value supply residual) := by
  have m1 := mem.write 128 value (Or.inr (by decide))
  rw [show memExtSize 192 128 32 = 192 from by decide] at m1
  have ptr0 := mem.word
  have ptr1 := m1.word
  dsimp only [memWord] at ptr0 ptr1
  have h := run.cut
  unfold t_2a02_c63 at h
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
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl, mem.read_self (by decide : 64 + 32 ≤ 192), ptr0] at hd
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
  simp only [show (64 : B256).toNat = 64 from rfl, m1.read_self (by decide : 64 + 32 ≤ 192), ptr1] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := fromWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word fromWord) (ri_and hd)
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
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 32) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  simp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_log3 hd
  simp only [show (128 : B256).toNat = 128 from rfl, show (32 : B256).toNat = 32 from rfl,
    m1.read_self (by decide : 128 + 32 ≤ 192), Mem.read_write_word_of_wf mem.wf 128 value] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨residual, eq⟩ := ric_ret h
  exact ⟨nonstatic, residual, Seg.done.inj eq⟩

def lpBurnBalanceBase (sevm : Sevm) (b : Devm) (fromWord debited : B256) : Devm :=
  afterSstore sevm b (transferBalanceSlot fromWord.toAdr) debited

def lpBurnSupplyWord (sevm : Sevm) (b : Devm) (fromWord debited : B256) : B256 :=
  (lpBurnBalanceBase sevm b fromWord debited).getStorVal sevm.currentTarget 0

def lpBurnBalancePost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (fromWord value debited : B256) (G : Nat) : Devm :=
  lpBurnSupplyPost sevm (afterSload sevm (lpBurnBalanceBase sevm b fromWord debited) 0) R
    ((M.write 0 fromWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes)
    fromWord value (lpBurnSupplyWord sevm b fromWord debited - value) G

/-- The balance store precedes the supply load, including a raw hash alias at slot zero. -/
theorem lpBurn_balance_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G balanceCost loadCost supplyCost : Nat} {fromWord value debited ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (balanceEq : balanceCost = sstoreCost sevm b (transferBalanceSlot fromWord.toAdr) debited)
    (loadEq : loadCost = sloadCost sevm (lpBurnBalanceBase sevm b fromWord debited) 0)
    (supplyEq : supplyCost = sstoreCost sevm
      (afterSload sevm (lpBurnBalanceBase sevm b fromWord debited) 0) 0
      (lpBurnSupplyWord sevm b fromWord debited - value))
    (balanceSentry : gCallStipend < G + balanceCost + loadCost + supplyCost + 1921)
    (supplySentry : gCallStipend < G + supplyCost + 1831)
    (nonstatic : sevm.isStatic = false)
    (cover : value ≤ lpBurnSupplyWord sevm b fromWord debited)
    (room : R.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (debited :: value :: fromWord :: ρ :: R)
      M (G + balanceCost + loadCost + supplyCost + 2009)) t_29c8_c63
      (.returned (lpBurnBalancePost sevm b R M fromWord value debited G)) := by
  have m0 := mem.write 0 fromWord.toAdr.toB256 (Or.inl (by decide))
  rw [show memExtSize 192 0 32 = 192 from by decide] at m0
  have m1 := lpMintScratch_ptr mem fromWord
  unfold t_29c8_c63
  refine rx_dest ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 3) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := fromWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word fromWord)
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
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  simp only [show (0 : B256).toNat = 0 from rfl, show (32 : B256).toNat = 32 from rfl]
  have gh : G + balanceCost + loadCost + supplyCost + 1972 =
    (G + balanceCost + loadCost + supplyCost + 1930) + 42 := by omega
  rw [gh]
  refine rx_keccak (v := transferBalanceSlot fromWord.toAdr) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m1.size]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 fromWord.toAdr.toB256 1)
  refine rx_swap2 ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  have gs : G + balanceCost + loadCost + supplyCost + 1921 =
    (G + loadCost + supplyCost + 1921) + balanceCost := by omega
  rw [gs]
  refine rx_sstoreC fork balanceEq (by omega) nonstatic ?_
  have gl : G + loadCost + supplyCost + 1921 = (G + supplyCost + 1921) + loadCost := by omega
  rw [gl]
  refine rx_sload_selC fork loadEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x2a02) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x226e) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0x226e) (by decide) (by simp only [List.length_cons]; omega) ?_
  have gc : G + supplyCost + 1903 = ((G + supplyCost + 1841) + 54) + 8 := by omega
  rw [gc]
  refine rx_callRet (g := t_226e_c59) rfl
    (sub59_exact cover (by simp only [List.length_cons]; omega)) ?_
  exact lpBurn_supply_exact fork m1 supplyEq supplySentry nonstatic room

/-- Inverse keeps the post-balance-write supply read and derives its checked debit. -/
theorem lpBurn_balance_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {fromWord value debited ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm (St b (debited :: value :: fromWord :: ρ :: R) M G) t_29c8_c63 o) :
    sevm.isStatic = false ∧ value ≤ lpBurnSupplyWord sevm b fromWord debited ∧
      ∃ residual, o = .returned (lpBurnBalancePost sevm b R M fromWord value debited residual) := by
  have m1 := lpMintScratch_ptr mem fromWord
  have hash := congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 fromWord.toAdr.toB256 1)
  have h := run.cut
  unfold t_29c8_c63 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := fromWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word fromWord) (ri_and hd)
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
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0x2a, 0x02] = (0x2a02 : B256) from by decide] at hd
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
  simp only [show Bytes.toB256 [0x22, 0x6e] = (0x226e : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0x226e) (by decide) (ri_and hd)
  obtain ⟨_, call⟩ := ric_call (g := t_226e_c59) rfl h
  rcases call with ⟨d, checked, tail⟩ | ⟨d, checked, _⟩
  · obtain ⟨cover, _, eq⟩ := sub59_inv checked
    cases eq
    obtain ⟨_, residual, result⟩ := lpBurn_supply_inv fork m1 tail.uncut
    exact ⟨nonstatic, cover, residual, result⟩
  · obtain ⟨_, _, eq⟩ := sub59_inv checked
    cases eq

def lpBurnBalanceWord (sevm : Sevm) (b : Devm) (fromWord : B256) : B256 :=
  b.getStorVal sevm.currentTarget (transferBalanceSlot fromWord.toAdr)

def lpBurnPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (fromWord value : B256) (G : Nat) : Devm :=
  lpBurnBalancePost sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr)) R
    ((M.write 0 fromWord.toAdr.toB256.toBytes).write 32 (1 : B256).toBytes)
    fromWord value (lpBurnBalanceWord sevm b fromWord - value) G

/-- Entry63 follows both checked subtractions with the actual sequential storage charges. -/
theorem lpBurn63_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G sourceCost balanceCost loadCost supplyCost : Nat} {fromWord value ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (sourceEq : sourceCost = sloadCost sevm b (transferBalanceSlot fromWord.toAdr))
    (balanceEq : balanceCost = sstoreCost sevm
      (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
      (transferBalanceSlot fromWord.toAdr) (lpBurnBalanceWord sevm b fromWord - value))
    (loadEq : loadCost = sloadCost sevm
      (lpBurnBalanceBase sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord sevm b fromWord - value)) 0)
    (supplyEq : supplyCost = sstoreCost sevm
      (afterSload sevm (lpBurnBalanceBase sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord sevm b fromWord - value)) 0) 0
      (lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord sevm b fromWord - value) - value))
    (balanceSentry : gCallStipend < G + balanceCost + loadCost + supplyCost + 1921)
    (supplySentry : gCallStipend < G + supplyCost + 1831)
    (nonstatic : sevm.isStatic = false)
    (balanceCover : value ≤ lpBurnBalanceWord sevm b fromWord)
    (supplyCover : value ≤ lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
      fromWord (lpBurnBalanceWord sevm b fromWord - value))
    (room : R.length ≤ 1014) :
    SFunc.RunExact cert.prog sevm (St b (value :: fromWord :: ρ :: R)
      M (G + sourceCost + balanceCost + loadCost + supplyCost + 2168)) t_2992_c63
      (.returned (lpBurnPost sevm b R M fromWord value G)) := by
  have m0 := mem.write 0 fromWord.toAdr.toB256 (Or.inl (by decide))
  rw [show memExtSize 192 0 32 = 192 from by decide] at m0
  have m1 := lpMintScratch_ptr mem fromWord
  unfold t_2992_c63
  refine rx_dest ?_
  refine rx_push (w := ~~~ addressMask) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := fromWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word fromWord)
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
  have gh : G + sourceCost + balanceCost + loadCost + supplyCost + 2131 =
    (G + sourceCost + balanceCost + loadCost + supplyCost + 2089) + 42 := by omega
  rw [gh]
  refine rx_keccak (v := transferBalanceSlot fromWord.toAdr) (c := 42) ?_ ?_
    (m1.read_self (by decide)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m1.size]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 fromWord.toAdr.toB256 1)
  have gl : G + sourceCost + balanceCost + loadCost + supplyCost + 2089 =
    (G + balanceCost + loadCost + supplyCost + 2089) + sourceCost := by omega
  rw [gl]
  refine rx_sload_selC fork sourceEq (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x29c8) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0xffffffff) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x226e) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := 0x226e) (by decide) (by simp only [List.length_cons]; omega) ?_
  have gc : G + balanceCost + loadCost + supplyCost + 2071 =
    ((G + balanceCost + loadCost + supplyCost + 2009) + 54) + 8 := by omega
  rw [gc]
  refine rx_callRet (g := t_226e_c59) rfl
    (sub59_exact balanceCover (by simp only [List.length_cons]; omega)) ?_
  exact lpBurn_balance_exact fork m1 balanceEq loadEq supplyEq balanceSentry supplySentry
    nonstatic supplyCover room

/-- Successful entry63 derives both covers and its sequential raw world, without hash separation. -/
theorem lpBurn63_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {fromWord value ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 192 M)
    (run : SFunc.Run cert.prog sevm (St b (value :: fromWord :: ρ :: R) M G) t_2992_c63 o) :
    sevm.isStatic = false ∧ value ≤ lpBurnBalanceWord sevm b fromWord ∧
      value ≤ lpBurnSupplyWord sevm (afterSload sevm b (transferBalanceSlot fromWord.toAdr))
        fromWord (lpBurnBalanceWord sevm b fromWord - value) ∧
      ∃ residual, o = .returned (lpBurnPost sevm b R M fromWord value residual) := by
  have m1 := lpMintScratch_ptr mem fromWord
  have hash := congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 fromWord.toAdr.toB256 1)
  have h := run.cut
  unfold t_2992_c63 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  simp only [show Bytes.toB256 [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff] = (~~~ addressMask : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := fromWord.toAdr.toB256)
    (by rw [B256.and_comm]; exact ff20_and_word fromWord) (ri_and hd)
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
  simp only [show Bytes.toB256 [0x29, 0xc8] = (0x29c8 : B256) from by decide] at hd
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
  simp only [show Bytes.toB256 [0x22, 0x6e] = (0x226e : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0x226e) (by decide) (ri_and hd)
  obtain ⟨_, call⟩ := ric_call (g := t_226e_c59) rfl h
  rcases call with ⟨d, checked, tail⟩ | ⟨d, checked, _⟩
  · obtain ⟨balanceCover, _, eq⟩ := sub59_inv checked
    cases eq
    obtain ⟨nonstatic, supplyCover, residual, result⟩ := lpBurn_balance_inv fork m1 tail.uncut
    exact ⟨nonstatic, balanceCover, supplyCover, residual, result⟩
  · obtain ⟨_, _, eq⟩ := sub59_inv checked
    cases eq

end Blanc.Lift.UniswapV2Pair
