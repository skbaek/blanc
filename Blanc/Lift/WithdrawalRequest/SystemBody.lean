import Blanc.Lift.WithdrawalRequest.SystemSetup
import Blanc.Lift.WithdrawalRequest.SystemAmount
import Blanc.Lift.WithdrawalRequest.SystemMemory
import Blanc.Lift.ExactWalkOps

/-! # Certified one-record queue body, retaining raw word and memory effects -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

/-- The actual modulo-word key arithmetic, without a coherent-pointer premise. -/
def systemBodyKey (head index : B256) : B256 := 4 + 3 * (index + head)

def systemBodyBase1 (sevm : Sevm) (base : Devm) (head index : B256) : Devm :=
  afterSload sevm base (systemBodyKey head index)

def systemBodyBase2 (sevm : Sevm) (base : Devm) (head index : B256) : Devm :=
  afterSload sevm (systemBodyBase1 sevm base head index) (1 + systemBodyKey head index)

def systemBodyBase (sevm : Sevm) (base : Devm) (head index : B256) : Devm :=
  afterSload sevm (systemBodyBase2 sevm base head index) (2 + systemBodyKey head index)

def systemBodyCaller (sevm : Sevm) (base : Devm) (head index : B256) : B256 :=
  base.getStorVal sevm.currentTarget (systemBodyKey head index)

def systemBodyPubkey (sevm : Sevm) (base : Devm) (head index : B256) : B256 :=
  (systemBodyBase1 sevm base head index).getStorVal sevm.currentTarget
    (1 + systemBodyKey head index)

def systemBodyPacked (sevm : Sevm) (base : Devm) (head index : B256) : B256 :=
  (systemBodyBase2 sevm base head index).getStorVal sevm.currentTarget
    (2 + systemBodyKey head index)

def systemBodyMemory (sevm : Sevm) (base : Devm) (head index : B256) (memory : Mem) : Mem :=
  systemRecordMemory index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory

/-- Both certified copies of the body execute the identical one-record tree. -/
theorem systemBody_tree_eq : t_00e9_c1 = t_00e9_c6 := rfl


/-- Named continuation extracted from the certified body. -/
def systemBodyWord2Tree : SFunc :=
  match t_00e9_c1 with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f)))))))))))))))))) => f
  | _ => .undefined

private theorem systemBodyWord2Tree_split : t_00e9_c1 = (.next (.reg (.dup 2)) (.next (.reg (.dup 1)) (.next (.reg .add) (.next (.push [0x03] (by decide)) (.next (.reg .mul) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next (.reg (.dup 1)) (.next (.push [0x4c] (by decide)) (.next (.reg .mul) (.next (.reg (.dup 1)) (.next (.reg .sload) (.next (.push [0x60] (by decide)) (.next (.reg .shl) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x14] (by decide)) (.next (.reg .add) systemBodyWord2Tree)))))))))))))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyWord3Tree : SFunc :=
  match systemBodyWord2Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f)))))))) => f
  | _ => .undefined

private theorem systemBodyWord3Tree_split : systemBodyWord2Tree = (.next (.reg (.dup 1)) (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.reg .sload) (.next (.reg (.dup 1)) (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.reg .add) systemBodyWord3Tree)))))))) := rfl

/-- Named continuation extracted from the certified body. -/
private theorem systemBodyAmountTree_split : systemBodyWord3Tree = (.next (.reg (.swap 0)) (.next (.push [0x02] (by decide)) (.next (.reg .add) (.next (.reg .sload) (.next (.reg (.dup 0)) (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00] (by decide)) (.next (.reg .and) (.next (.reg (.dup 2)) (.next (.reg .mstore) systemBodyAmountTree))))))))) := rfl

private theorem systemBody_word1_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [index, count, head, tail] memory gas) t_00e9_c1 out) :
    ∃ gas', SFunc.Run prog sevm
      (St (systemBodyBase1 sevm base head index) [systemRecordPubkeyOffset index, systemBodyKey head index, index, count, head, tail] (memory.write (systemRecordOffset index).toNat (systemBodyCaller sevm base head index <<< 96).toBytes) gas') systemBodyWord2Tree out := by
  have run0 := run.cut
  clear run
  rw [systemBodyWord2Tree_split] at run0
  obtain ⟨d, step, run1⟩ := ric_next run0
  clear run0
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run2⟩ := ric_next run1
  clear run1
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run3⟩ := ric_next run2
  clear run2
  obtain ⟨_, rfl⟩ := ri_add step
  clear step
  obtain ⟨d, step, run4⟩ := ric_next run3
  clear run3
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run5⟩ := ric_next run4
  clear run4
  obtain ⟨_, rfl⟩ := ri_mul step
  clear step
  obtain ⟨d, step, run6⟩ := ric_next run5
  clear run5
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run7⟩ := ric_next run6
  clear run6
  obtain ⟨_, rfl⟩ := ri_val (w := systemBodyKey head index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run8⟩ := ric_next run7
  clear run7
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run9⟩ := ric_next run8
  clear run8
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run10⟩ := ric_next run9
  clear run9
  obtain ⟨_, rfl⟩ := ri_val (w := systemRecordOffset index) rfl (ri_mul step)
  clear step
  obtain ⟨d, step, run11⟩ := ric_next run10
  clear run10
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run12⟩ := ric_next run11
  clear run11
  obtain ⟨_, rfl⟩ := ri_val (w := systemBodyCaller sevm base head index) rfl (ri_sload fork step)
  clear step
  obtain ⟨d, step, run13⟩ := ric_next run12
  clear run12
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run14⟩ := ric_next run13
  clear run13
  obtain ⟨_, rfl⟩ := ri_val (w := systemBodyCaller sevm base head index <<< 96) rfl (ri_shl step)
  clear step
  obtain ⟨d, step, run15⟩ := ric_next run14
  clear run14
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run16⟩ := ric_next run15
  clear run15
  obtain ⟨_, rfl⟩ := ri_mstore step
  clear step
  obtain ⟨d, step, run17⟩ := ric_next run16
  clear run16
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run18⟩ := ric_next run17
  clear run17
  obtain ⟨_, rfl⟩ := ri_val (w := systemRecordPubkeyOffset index) rfl (ri_add step)
  clear step
  exact ⟨_, run18.uncut⟩

private theorem systemBody_word2_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [systemRecordPubkeyOffset index, systemBodyKey head index, index, count, head, tail] memory gas) systemBodyWord2Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St (afterSload sevm base (1 + systemBodyKey head index)) [systemRecordSuffixOffset index, systemBodyKey head index, index, count, head, tail] (memory.write (systemRecordPubkeyOffset index).toNat (base.getStorVal sevm.currentTarget (1 + systemBodyKey head index)).toBytes) gas') systemBodyWord3Tree out := by
  have run18 := run.cut
  clear run
  rw [systemBodyWord3Tree_split] at run18
  obtain ⟨d, step, run19⟩ := ric_next run18
  clear run18
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run20⟩ := ric_next run19
  clear run19
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run21⟩ := ric_next run20
  clear run20
  obtain ⟨_, rfl⟩ := ri_val (w := 1 + systemBodyKey head index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run22⟩ := ric_next run21
  clear run21
  obtain ⟨_, rfl⟩ := ri_sload fork step
  clear step
  obtain ⟨d, step, run23⟩ := ric_next run22
  clear run22
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run24⟩ := ric_next run23
  clear run23
  obtain ⟨_, rfl⟩ := ri_mstore step
  clear step
  obtain ⟨d, step, run25⟩ := ric_next run24
  clear run24
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run26⟩ := ric_next run25
  clear run25
  obtain ⟨_, rfl⟩ := ri_val (w := systemRecordSuffixOffset index) rfl (ri_add step)
  clear step
  exact ⟨_, run26.uncut⟩

private theorem systemBody_word3_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [systemRecordSuffixOffset index, systemBodyKey head index, index, count, head, tail] memory gas) systemBodyWord3Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St (afterSload sevm base (2 + systemBodyKey head index)) [base.getStorVal sevm.currentTarget (2 + systemBodyKey head index), systemRecordSuffixOffset index, index, count, head, tail] (memory.write (systemRecordSuffixOffset index).toNat (systemPubkeyMask &&& base.getStorVal sevm.currentTarget (2 + systemBodyKey head index)).toBytes) gas') systemBodyAmountTree out := by
  have run26 := run.cut
  clear run
  rw [systemBodyAmountTree_split] at run26
  obtain ⟨d, step, run27⟩ := ric_next run26
  clear run26
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  clear step
  obtain ⟨d, step, run28⟩ := ric_next run27
  clear run27
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run29⟩ := ric_next run28
  clear run28
  obtain ⟨_, rfl⟩ := ri_val (w := 2 + systemBodyKey head index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run30⟩ := ric_next run29
  clear run29
  obtain ⟨_, rfl⟩ := ri_sload fork step
  clear step
  obtain ⟨d, step, run31⟩ := ric_next run30
  clear run30
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run32⟩ := ric_next run31
  clear run31
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run33⟩ := ric_next run32
  clear run32
  obtain ⟨_, rfl⟩ := ri_val (w := systemPubkeyMask &&& base.getStorVal sevm.currentTarget (2 + systemBodyKey head index)) rfl (ri_and step)
  clear step
  obtain ⟨d, step, run34⟩ := ric_next run33
  clear run33
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run35⟩ := ric_next run34
  clear run34
  obtain ⟨_, rfl⟩ := ri_mstore step
  clear step
  exact ⟨_, run35.uncut⟩

/-- A successful body reaches the next canonical header with the entire actual state. -/
theorem systemBody_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run prog sevm (St base [index, count, head, tail] memory gas)
      t_00e9_c1 out) :
    ∃ gas', SFunc.Run prog sevm
      (St (systemBodyBase sevm base head index) [1 + index, count, head, tail]
        (systemBodyMemory sevm base head index memory) gas') t_00e1_c6 out := by
  simp only [systemBodyMemory, systemRecordMemory, systemRecordStage,
    MemoryStage.applyMemory_append, systemRecordWordStage,
    MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]
  obtain ⟨_, run⟩ := systemBody_word1_inv fork run
  obtain ⟨_, run⟩ := systemBody_word2_inv fork run
  obtain ⟨_, run⟩ := systemBody_word3_inv fork run
  exact systemBody_amount_inv run


/-- Memory immediately after the three word stores, before the amount overwrites. -/
def systemBodyWordMemory (sevm : Sevm) (base : Devm) (head index : B256) (memory : Mem) : Mem :=
  (systemRecordWordStage index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index)).applyMemory memory

/-- Exact body charge from pinned instructions and each selected dynamic access. -/
def systemBodyGas (sevm : Sevm) (base : Devm) (head index : B256) (memory : Mem) : Nat :=
  27 * gVerylow + 2 * gLow +
  sloadCost sevm base (systemBodyKey head index) +
  sloadCost sevm (systemBodyBase1 sevm base head index) (1 + systemBodyKey head index) +
  sloadCost sevm (systemBodyBase2 sevm base head index) (2 + systemBodyKey head index) +
  systemRecordWordCharge index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 0 +
  systemRecordWordCharge index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 1 +
  systemRecordWordCharge index (systemBodyCaller sevm base head index)
    (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 2 +
  systemBodyAmountGas index (systemBodyPacked sevm base head index)
    (systemBodyWordMemory sevm base head index memory)

private theorem systemBody_word1_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (systemRecordOffset index).toNat 32)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm (St (systemBodyBase1 sevm base head index) [systemRecordPubkeyOffset index, systemBodyKey head index, index, count, head, tail] (memory.write (systemRecordOffset index).toNat (systemBodyCaller sevm base head index <<< 96).toBytes) gas) systemBodyWord2Tree out) :
    SFunc.RunExact prog sevm
      (St base [index, count, head, tail] memory (gas + 52 + sloadCost sevm base (systemBodyKey head index) + c)) t_00e9_c1 out := by
  have gasEq : gas + 52 + sloadCost sevm base (systemBodyKey head index) + c = gas + 3 + 3 + c + 3 + 3 + 3 + sloadCost sevm base (systemBodyKey head index) + 3 + 5 + 3 + 3 + 3 + 3 + 5 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyWord2Tree_split]
  apply rx_dup3 (by change 4 < 1024; decide)
  apply rx_dup2 (by change 5 < 1024; decide)
  apply rx_add' (v := index + head) rfl (by change 4 < 1024; decide)
  apply rx_push rfl (by change 5 < 1024; decide)
  apply rx_mul (v := 3 * (index + head)) rfl (by change 4 < 1024; decide)
  apply rx_push rfl (by change 5 < 1024; decide)
  apply rx_add' (v := systemBodyKey head index) rfl (by change 4 < 1024; decide)
  apply rx_dup2 (by change 5 < 1024; decide)
  apply rx_push rfl (by change 6 < 1024; decide)
  apply rx_mul (v := systemRecordOffset index) rfl (by change 5 < 1024; decide)
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_sload_sel fork (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shl (v := systemBodyCaller sevm base head index <<< 96) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_mstore (Devm.extCost_add_of_size rfl charge) rfl
  apply rx_push rfl (by change 6 < 1024; decide)
  apply rx_add' (v := systemRecordPubkeyOffset index) rfl (by change 5 < 1024; decide)
  exact next

private theorem systemBody_word2_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (systemRecordPubkeyOffset index).toNat 32)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm (St (afterSload sevm base (1 + systemBodyKey head index)) [systemRecordSuffixOffset index, systemBodyKey head index, index, count, head, tail] (memory.write (systemRecordPubkeyOffset index).toNat (base.getStorVal sevm.currentTarget (1 + systemBodyKey head index)).toBytes) gas) systemBodyWord3Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordPubkeyOffset index, systemBodyKey head index, index, count, head, tail] memory (gas + 18 + sloadCost sevm base (1 + systemBodyKey head index) + c)) systemBodyWord2Tree out := by
  have gasEq : gas + 18 + sloadCost sevm base (1 + systemBodyKey head index) + c = gas + 3 + 3 + c + 3 + sloadCost sevm base (1 + systemBodyKey head index) + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyWord3Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_add' (v := 1 + systemBodyKey head index) rfl (by change 6 < 1024; decide)
  apply rx_sload_sel fork (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_mstore (Devm.extCost_add_of_size rfl charge) rfl
  apply rx_push rfl (by change 6 < 1024; decide)
  apply rx_add' (v := systemRecordSuffixOffset index) rfl (by change 5 < 1024; decide)
  exact next

private theorem systemBody_word3_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (systemRecordSuffixOffset index).toNat 32)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm (St (afterSload sevm base (2 + systemBodyKey head index)) [base.getStorVal sevm.currentTarget (2 + systemBodyKey head index), systemRecordSuffixOffset index, index, count, head, tail] (memory.write (systemRecordSuffixOffset index).toNat (systemPubkeyMask &&& base.getStorVal sevm.currentTarget (2 + systemBodyKey head index)).toBytes) gas) systemBodyAmountTree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordSuffixOffset index, systemBodyKey head index, index, count, head, tail] memory (gas + 21 + sloadCost sevm base (2 + systemBodyKey head index) + c)) systemBodyWord3Tree out := by
  have gasEq : gas + 21 + sloadCost sevm base (2 + systemBodyKey head index) + c = gas + c + 3 + 3 + 3 + 3 + sloadCost sevm base (2 + systemBodyKey head index) + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyAmountTree_split]
  apply rx_swap1
  apply rx_push rfl (by change 6 < 1024; decide)
  apply rx_add' (v := 2 + systemBodyKey head index) rfl (by change 5 < 1024; decide)
  apply rx_sload_sel fork (by change 5 < 1024; decide)
  apply rx_dup1 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_and (v := systemPubkeyMask &&& base.getStorVal sevm.currentTarget (2 + systemBodyKey head index)) rfl (by change 6 < 1024; decide)
  apply rx_dup3 (by change 7 < 1024; decide)
  apply rx_mstore (Devm.extCost_add_of_size rfl charge) rfl
  exact next

/-- An exact next-header continuation constructs all actual body instructions. -/
theorem systemBody_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (next : SFunc.RunExact prog sevm
      (St (systemBodyBase sevm base head index) [1 + index, count, head, tail]
        (systemBodyMemory sevm base head index memory) gas) t_00e1_c6 out) :
    SFunc.RunExact prog sevm (St base [index, count, head, tail]
      memory (gas + systemBodyGas sevm base head index memory)) t_00e9_c1 out := by
  let m1 : Mem := memory.write (systemRecordOffset index).toNat
    (systemBodyCaller sevm base head index <<< 96).toBytes
  let m2 : Mem := m1.write (systemRecordPubkeyOffset index).toNat
    (systemBodyPubkey sevm base head index).toBytes
  let m3 : Mem := m2.write (systemRecordSuffixOffset index).toNat
    (systemPubkeyMask &&& systemBodyPacked sevm base head index).toBytes
  simp only [systemBodyMemory, systemRecordMemory, systemRecordStage,
    MemoryStage.applyMemory_append, systemRecordWordStage,
    MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil] at next
  have amount := systemBody_amount_exact
    (base := systemBodyBase sevm base head index) (memory := m3)
    (packed := systemBodyPacked sevm base head index) next
  have words := systemBody_word3_exact (base := systemBodyBase2 sevm base head index) (memory := m2)
    (c := systemRecordWordCharge index (systemBodyCaller sevm base head index)
      (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 2) fork
    (by simp only [systemRecordWordCharge, systemRecordWordStage, List.getElem?_cons_succ,
      List.getElem?_cons_zero, B256.length_toBytes, List.take_succ_cons, List.take_zero,
      MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) amount
  have words := systemBody_word2_exact (base := systemBodyBase1 sevm base head index) (memory := m1)
    (c := systemRecordWordCharge index (systemBodyCaller sevm base head index)
      (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 1) fork
    (by simp only [systemRecordWordCharge, systemRecordWordStage, List.getElem?_cons_succ,
      List.getElem?_cons_zero, B256.length_toBytes, List.take_succ_cons, List.take_zero,
      MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) words
  have ready := systemBody_word1_exact (base := base) (memory := memory)
    (c := systemRecordWordCharge index (systemBodyCaller sevm base head index)
      (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 0) fork
    (by simp only [systemRecordWordCharge, systemRecordWordStage, List.getElem?_cons_zero,
      B256.length_toBytes, List.take_zero, MemoryStage.applyMemory_nil]) words
  have gasEq : gas + systemBodyGas sevm base head index memory =
      gas + systemBodyAmountGas index (systemBodyPacked sevm base head index) m3
      + 21 + sloadCost sevm (systemBodyBase2 sevm base head index) (2 + systemBodyKey head index)
      + systemRecordWordCharge index (systemBodyCaller sevm base head index)
      (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 2
      + 18 + sloadCost sevm (systemBodyBase1 sevm base head index) (1 + systemBodyKey head index)
      + systemRecordWordCharge index (systemBodyCaller sevm base head index)
      (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 1
      + 52 + sloadCost sevm base (systemBodyKey head index)
      + systemRecordWordCharge index (systemBodyCaller sevm base head index)
      (systemBodyPubkey sevm base head index) (systemBodyPacked sevm base head index) memory 0 := by
    unfold systemBodyGas
    simp only [gVerylow, gLow, systemBodyWordMemory, systemRecordWordStage,
      MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]
    unfold m3 m2 m1
    omega
  rw [gasEq]
  exact ready

/-- The canonical backedge body's identical tree consumes the same exact interface. -/
theorem systemBody_exact_c6 {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {out : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (next : SFunc.RunExact prog sevm
      (St (systemBodyBase sevm base head index) [1 + index, count, head, tail]
        (systemBodyMemory sevm base head index memory) gas) t_00e1_c6 out) :
    SFunc.RunExact prog sevm (St base [index, count, head, tail]
      memory (gas + systemBodyGas sevm base head index memory)) t_00e9_c6 out := by
  rw [← systemBody_tree_eq]
  exact systemBody_exact fork next

end Blanc.Lift.WithdrawalRequest
