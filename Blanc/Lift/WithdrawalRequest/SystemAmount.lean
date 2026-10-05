import Blanc.Lift.WithdrawalRequest.SystemSetup
import Blanc.Lift.WithdrawalRequest.SystemMemory
import Blanc.Lift.ExactWalkOps

/-! # The certified queue body's decreasing-offset amount stores -/

namespace Blanc.Lift.WithdrawalRequest

open Jaune

theorem systemBody_loop_lookup : prog[6]? = some t_00e1_c6 := rfl

def systemBodyAmountTree : SFunc :=
  match t_00e9_c1 with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))))))))))))))))))))))))))))))) => f
  | _ => .undefined

/-- Named continuation extracted from the certified body. -/
def systemBodyByte7Tree : SFunc :=
  match systemBodyAmountTree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte7Tree_split : systemBodyAmountTree = (.next (.reg (.swap 0)) (.next (.push [0x10] (by decide)) (.next (.reg .add) (.next (.reg (.swap 0)) (.next (.push [0x40] (by decide)) (.next (.reg .shr) (.next (.reg (.swap 0)) systemBodyByte7Tree))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyByte6Tree : SFunc :=
  match systemBodyByte7Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte6Tree_split : systemBodyByte7Tree = (.next (.reg (.dup 1)) (.next (.push [0x38] (by decide)) (.next (.reg .shr) (.next (.reg (.dup 1)) (.next (.push [0x07] (by decide)) (.next (.reg .add) (.next (.reg .mstore8) systemBodyByte6Tree))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyByte5Tree : SFunc :=
  match systemBodyByte6Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte5Tree_split : systemBodyByte6Tree = (.next (.reg (.dup 1)) (.next (.push [0x30] (by decide)) (.next (.reg .shr) (.next (.reg (.dup 1)) (.next (.push [0x06] (by decide)) (.next (.reg .add) (.next (.reg .mstore8) systemBodyByte5Tree))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyByte4Tree : SFunc :=
  match systemBodyByte5Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte4Tree_split : systemBodyByte5Tree = (.next (.reg (.dup 1)) (.next (.push [0x28] (by decide)) (.next (.reg .shr) (.next (.reg (.dup 1)) (.next (.push [0x05] (by decide)) (.next (.reg .add) (.next (.reg .mstore8) systemBodyByte4Tree))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyByte3Tree : SFunc :=
  match systemBodyByte4Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte3Tree_split : systemBodyByte4Tree = (.next (.reg (.dup 1)) (.next (.push [0x20] (by decide)) (.next (.reg .shr) (.next (.reg (.dup 1)) (.next (.push [0x04] (by decide)) (.next (.reg .add) (.next (.reg .mstore8) systemBodyByte3Tree))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyByte2Tree : SFunc :=
  match systemBodyByte3Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte2Tree_split : systemBodyByte3Tree = (.next (.reg (.dup 1)) (.next (.push [0x18] (by decide)) (.next (.reg .shr) (.next (.reg (.dup 1)) (.next (.push [0x03] (by decide)) (.next (.reg .add) (.next (.reg .mstore8) systemBodyByte2Tree))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyByte1Tree : SFunc :=
  match systemBodyByte2Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte1Tree_split : systemBodyByte2Tree = (.next (.reg (.dup 1)) (.next (.push [0x10] (by decide)) (.next (.reg .shr) (.next (.reg (.dup 1)) (.next (.push [0x02] (by decide)) (.next (.reg .add) (.next (.reg .mstore8) systemBodyByte1Tree))))))) := rfl

/-- Named continuation extracted from the certified body. -/
def systemBodyByte0Tree : SFunc :=
  match systemBodyByte1Tree with
  | (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ (.next _ f))))))) => f
  | _ => .undefined

private theorem systemBodyByte0Tree_split : systemBodyByte1Tree = (.next (.reg (.dup 1)) (.next (.push [0x08] (by decide)) (.next (.reg .shr) (.next (.reg (.dup 1)) (.next (.push [0x01] (by decide)) (.next (.reg .add) (.next (.reg .mstore8) systemBodyByte0Tree))))))) := rfl

private theorem systemBody_amount_prep_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [packed, systemRecordSuffixOffset index, index, count, head, tail] memory gas) systemBodyAmountTree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas') systemBodyByte7Tree out := by
  have run35 := run.cut
  clear run
  rw [systemBodyByte7Tree_split] at run35
  obtain ⟨d, step, run36⟩ := ric_next run35
  clear run35
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  clear step
  obtain ⟨d, step, run37⟩ := ric_next run36
  clear run36
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run38⟩ := ric_next run37
  clear run37
  obtain ⟨_, rfl⟩ := ri_val (w := systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run39⟩ := ric_next run38
  clear run38
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  clear step
  obtain ⟨d, step, run40⟩ := ric_next run39
  clear run39
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run41⟩ := ric_next run40
  clear run40
  obtain ⟨_, rfl⟩ := ri_val (w := packed >>> 64) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run42⟩ := ric_next run41
  clear run41
  obtain ⟨_, rfl⟩ := ri_swap rfl step
  clear step
  exact ⟨_, run42.uncut⟩

private theorem systemBody_byte7_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte7Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] (memory.write (7 + systemRecordAmountOffset index).toNat [((packed >>> 64) >>> 56).2.2.toUInt8]) gas') systemBodyByte6Tree out := by
  have run42 := run.cut
  clear run
  rw [systemBodyByte6Tree_split] at run42
  obtain ⟨d, step, run43⟩ := ric_next run42
  clear run42
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run44⟩ := ric_next run43
  clear run43
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run45⟩ := ric_next run44
  clear run44
  obtain ⟨_, rfl⟩ := ri_val (w := (packed >>> 64) >>> 56) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run46⟩ := ric_next run45
  clear run45
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run47⟩ := ric_next run46
  clear run46
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run48⟩ := ric_next run47
  clear run47
  obtain ⟨_, rfl⟩ := ri_val (w := 7 + systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run49⟩ := ric_next run48
  clear run48
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  exact ⟨_, run49.uncut⟩

private theorem systemBody_byte6_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte6Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] (memory.write (6 + systemRecordAmountOffset index).toNat [((packed >>> 64) >>> 48).2.2.toUInt8]) gas') systemBodyByte5Tree out := by
  have run49 := run.cut
  clear run
  rw [systemBodyByte5Tree_split] at run49
  obtain ⟨d, step, run50⟩ := ric_next run49
  clear run49
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run51⟩ := ric_next run50
  clear run50
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run52⟩ := ric_next run51
  clear run51
  obtain ⟨_, rfl⟩ := ri_val (w := (packed >>> 64) >>> 48) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run53⟩ := ric_next run52
  clear run52
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run54⟩ := ric_next run53
  clear run53
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run55⟩ := ric_next run54
  clear run54
  obtain ⟨_, rfl⟩ := ri_val (w := 6 + systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run56⟩ := ric_next run55
  clear run55
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  exact ⟨_, run56.uncut⟩

private theorem systemBody_byte5_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte5Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] (memory.write (5 + systemRecordAmountOffset index).toNat [((packed >>> 64) >>> 40).2.2.toUInt8]) gas') systemBodyByte4Tree out := by
  have run56 := run.cut
  clear run
  rw [systemBodyByte4Tree_split] at run56
  obtain ⟨d, step, run57⟩ := ric_next run56
  clear run56
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run58⟩ := ric_next run57
  clear run57
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run59⟩ := ric_next run58
  clear run58
  obtain ⟨_, rfl⟩ := ri_val (w := (packed >>> 64) >>> 40) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run60⟩ := ric_next run59
  clear run59
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run61⟩ := ric_next run60
  clear run60
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run62⟩ := ric_next run61
  clear run61
  obtain ⟨_, rfl⟩ := ri_val (w := 5 + systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run63⟩ := ric_next run62
  clear run62
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  exact ⟨_, run63.uncut⟩

private theorem systemBody_byte4_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte4Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] (memory.write (4 + systemRecordAmountOffset index).toNat [((packed >>> 64) >>> 32).2.2.toUInt8]) gas') systemBodyByte3Tree out := by
  have run63 := run.cut
  clear run
  rw [systemBodyByte3Tree_split] at run63
  obtain ⟨d, step, run64⟩ := ric_next run63
  clear run63
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run65⟩ := ric_next run64
  clear run64
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run66⟩ := ric_next run65
  clear run65
  obtain ⟨_, rfl⟩ := ri_val (w := (packed >>> 64) >>> 32) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run67⟩ := ric_next run66
  clear run66
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run68⟩ := ric_next run67
  clear run67
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run69⟩ := ric_next run68
  clear run68
  obtain ⟨_, rfl⟩ := ri_val (w := 4 + systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run70⟩ := ric_next run69
  clear run69
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  exact ⟨_, run70.uncut⟩

private theorem systemBody_byte3_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte3Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] (memory.write (3 + systemRecordAmountOffset index).toNat [((packed >>> 64) >>> 24).2.2.toUInt8]) gas') systemBodyByte2Tree out := by
  have run70 := run.cut
  clear run
  rw [systemBodyByte2Tree_split] at run70
  obtain ⟨d, step, run71⟩ := ric_next run70
  clear run70
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run72⟩ := ric_next run71
  clear run71
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run73⟩ := ric_next run72
  clear run72
  obtain ⟨_, rfl⟩ := ri_val (w := (packed >>> 64) >>> 24) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run74⟩ := ric_next run73
  clear run73
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run75⟩ := ric_next run74
  clear run74
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run76⟩ := ric_next run75
  clear run75
  obtain ⟨_, rfl⟩ := ri_val (w := 3 + systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run77⟩ := ric_next run76
  clear run76
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  exact ⟨_, run77.uncut⟩

private theorem systemBody_byte2_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte2Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] (memory.write (2 + systemRecordAmountOffset index).toNat [((packed >>> 64) >>> 16).2.2.toUInt8]) gas') systemBodyByte1Tree out := by
  have run77 := run.cut
  clear run
  rw [systemBodyByte1Tree_split] at run77
  obtain ⟨d, step, run78⟩ := ric_next run77
  clear run77
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run79⟩ := ric_next run78
  clear run78
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run80⟩ := ric_next run79
  clear run79
  obtain ⟨_, rfl⟩ := ri_val (w := (packed >>> 64) >>> 16) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run81⟩ := ric_next run80
  clear run80
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run82⟩ := ric_next run81
  clear run81
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run83⟩ := ric_next run82
  clear run82
  obtain ⟨_, rfl⟩ := ri_val (w := 2 + systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run84⟩ := ric_next run83
  clear run83
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  exact ⟨_, run84.uncut⟩

private theorem systemBody_byte1_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte1Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] (memory.write (1 + systemRecordAmountOffset index).toNat [((packed >>> 64) >>> 8).2.2.toUInt8]) gas') systemBodyByte0Tree out := by
  have run84 := run.cut
  clear run
  rw [systemBodyByte0Tree_split] at run84
  obtain ⟨d, step, run85⟩ := ric_next run84
  clear run84
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run86⟩ := ric_next run85
  clear run85
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run87⟩ := ric_next run86
  clear run86
  obtain ⟨_, rfl⟩ := ri_val (w := (packed >>> 64) >>> 8) rfl (ri_shr step)
  clear step
  obtain ⟨d, step, run88⟩ := ric_next run87
  clear run87
  obtain ⟨_, rfl⟩ := ri_dup rfl step
  clear step
  obtain ⟨d, step, run89⟩ := ric_next run88
  clear run88
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run90⟩ := ric_next run89
  clear run89
  obtain ⟨_, rfl⟩ := ri_val (w := 1 + systemRecordAmountOffset index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run91⟩ := ric_next run90
  clear run90
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  exact ⟨_, run91.uncut⟩

private theorem systemBody_byte0_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail : B256} {packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas) systemBodyByte0Tree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [1 + index, count, head, tail] (memory.write (systemRecordAmountOffset index).toNat [(packed >>> 64).2.2.toUInt8]) gas') t_00e1_c6 out := by
  have run91 := run.cut
  clear run
  unfold systemBodyByte0Tree at run91
  obtain ⟨d, step, run92⟩ := ric_next run91
  clear run91
  obtain ⟨_, rfl⟩ := ri_mstore8 step
  clear step
  obtain ⟨d, step, run93⟩ := ric_next run92
  clear run92
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨d, step, run94⟩ := ric_next run93
  clear run93
  obtain ⟨_, rfl⟩ := ri_val (w := 1 + index) rfl (ri_add step)
  clear step
  obtain ⟨d, step, run95⟩ := ric_next run94
  clear run94
  obtain ⟨_, rfl⟩ := ri_push step
  clear step
  obtain ⟨gas', nextHeader⟩ := ric_jump (by intro h; cases h) systemBody_loop_lookup run95
  exact ⟨gas', nextHeader.uncut⟩

/-- The actual amount write sequence, retaining all eight singleton writes. -/
theorem systemBody_amount_inv {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail packed : B256} {out : Outcome}
    (run : SFunc.Run prog sevm
      (St base [packed, systemRecordSuffixOffset index, index, count, head, tail] memory gas)
      systemBodyAmountTree out) :
    ∃ gas', SFunc.Run prog sevm
      (St base [1 + index, count, head, tail]
        ((systemRecordAmountStage index packed).applyMemory memory) gas') t_00e1_c6 out := by
  simp only [systemRecordAmountStage, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]
  obtain ⟨_, run⟩ := systemBody_amount_prep_inv run
  obtain ⟨_, run⟩ := systemBody_byte7_inv (packed := packed) run
  obtain ⟨_, run⟩ := systemBody_byte6_inv (packed := packed) run
  obtain ⟨_, run⟩ := systemBody_byte5_inv (packed := packed) run
  obtain ⟨_, run⟩ := systemBody_byte4_inv (packed := packed) run
  obtain ⟨_, run⟩ := systemBody_byte3_inv (packed := packed) run
  obtain ⟨_, run⟩ := systemBody_byte2_inv (packed := packed) run
  obtain ⟨_, run⟩ := systemBody_byte1_inv (packed := packed) run
  exact systemBody_byte0_inv (packed := packed) run


/-- Exact amount-store charges plus the pinned non-store suffix instructions. -/
def systemBodyAmountGas (index packed : B256) (memory : Mem) : Nat :=
  52 * gVerylow + gMid +
  systemRecordAmountCharge index packed memory 0 +
  systemRecordAmountCharge index packed memory 1 +
  systemRecordAmountCharge index packed memory 2 +
  systemRecordAmountCharge index packed memory 3 +
  systemRecordAmountCharge index packed memory 4 +
  systemRecordAmountCharge index packed memory 5 +
  systemRecordAmountCharge index packed memory 6 +
  systemRecordAmountCharge index packed memory 7

private theorem systemBody_amount_prep_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas : Nat} {index count head tail packed : B256} {out : Outcome}
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail] memory gas)
      systemBodyByte7Tree out) :
    SFunc.RunExact prog sevm
      (St base [packed, systemRecordSuffixOffset index, index, count, head, tail]
        memory (gas + 21)) systemBodyAmountTree out := by
  have gasEq : gas + 21 = gas + 3 + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte7Tree_split]
  apply rx_swap1
  apply rx_push rfl (by change 6 < 1024; decide)
  apply rx_add' (v := systemRecordAmountOffset index) rfl (by change 5 < 1024; decide)
  apply rx_swap1
  apply rx_push rfl (by change 6 < 1024; decide)
  apply rx_shr (v := packed >>> 64) rfl (by change 5 < 1024; decide)
  exact rx_swap1 next

private theorem systemBody_byte7_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (7 + systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        (memory.write (7 + systemRecordAmountOffset index).toNat
          [((packed >>> 64) >>> 56).2.2.toUInt8]) gas) systemBodyByte6Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + c + 18)) systemBodyByte7Tree out := by
  have gasEq : gas + c + 18 = gas + c + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte6Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shr (v := (packed >>> 64) >>> 56) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_push rfl (by change 8 < 1024; decide)
  apply rx_add' (v := 7 + systemRecordAmountOffset index) rfl (by change 7 < 1024; decide)
  exact rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl next

private theorem systemBody_byte6_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (6 + systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        (memory.write (6 + systemRecordAmountOffset index).toNat
          [((packed >>> 64) >>> 48).2.2.toUInt8]) gas) systemBodyByte5Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + c + 18)) systemBodyByte6Tree out := by
  have gasEq : gas + c + 18 = gas + c + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte5Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shr (v := (packed >>> 64) >>> 48) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_push rfl (by change 8 < 1024; decide)
  apply rx_add' (v := 6 + systemRecordAmountOffset index) rfl (by change 7 < 1024; decide)
  exact rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl next

private theorem systemBody_byte5_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (5 + systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        (memory.write (5 + systemRecordAmountOffset index).toNat
          [((packed >>> 64) >>> 40).2.2.toUInt8]) gas) systemBodyByte4Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + c + 18)) systemBodyByte5Tree out := by
  have gasEq : gas + c + 18 = gas + c + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte4Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shr (v := (packed >>> 64) >>> 40) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_push rfl (by change 8 < 1024; decide)
  apply rx_add' (v := 5 + systemRecordAmountOffset index) rfl (by change 7 < 1024; decide)
  exact rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl next

private theorem systemBody_byte4_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (4 + systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        (memory.write (4 + systemRecordAmountOffset index).toNat
          [((packed >>> 64) >>> 32).2.2.toUInt8]) gas) systemBodyByte3Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + c + 18)) systemBodyByte4Tree out := by
  have gasEq : gas + c + 18 = gas + c + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte3Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shr (v := (packed >>> 64) >>> 32) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_push rfl (by change 8 < 1024; decide)
  apply rx_add' (v := 4 + systemRecordAmountOffset index) rfl (by change 7 < 1024; decide)
  exact rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl next

private theorem systemBody_byte3_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (3 + systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        (memory.write (3 + systemRecordAmountOffset index).toNat
          [((packed >>> 64) >>> 24).2.2.toUInt8]) gas) systemBodyByte2Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + c + 18)) systemBodyByte3Tree out := by
  have gasEq : gas + c + 18 = gas + c + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte2Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shr (v := (packed >>> 64) >>> 24) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_push rfl (by change 8 < 1024; decide)
  apply rx_add' (v := 3 + systemRecordAmountOffset index) rfl (by change 7 < 1024; decide)
  exact rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl next

private theorem systemBody_byte2_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (2 + systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        (memory.write (2 + systemRecordAmountOffset index).toNat
          [((packed >>> 64) >>> 16).2.2.toUInt8]) gas) systemBodyByte1Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + c + 18)) systemBodyByte2Tree out := by
  have gasEq : gas + c + 18 = gas + c + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte1Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shr (v := (packed >>> 64) >>> 16) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_push rfl (by change 8 < 1024; decide)
  apply rx_add' (v := 2 + systemRecordAmountOffset index) rfl (by change 7 < 1024; decide)
  exact rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl next

private theorem systemBody_byte1_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (1 + systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        (memory.write (1 + systemRecordAmountOffset index).toNat
          [((packed >>> 64) >>> 8).2.2.toUInt8]) gas) systemBodyByte0Tree out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + c + 18)) systemBodyByte1Tree out := by
  have gasEq : gas + c + 18 = gas + c + 3 + 3 + 3 + 3 + 3 + 3 := by omega
  rw [gasEq, systemBodyByte0Tree_split]
  apply rx_dup2 (by change 6 < 1024; decide)
  apply rx_push rfl (by change 7 < 1024; decide)
  apply rx_shr (v := (packed >>> 64) >>> 8) rfl (by change 6 < 1024; decide)
  apply rx_dup2 (by change 7 < 1024; decide)
  apply rx_push rfl (by change 8 < 1024; decide)
  apply rx_add' (v := 1 + systemRecordAmountOffset index) rfl (by change 7 < 1024; decide)
  exact rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl next

private theorem systemBody_byte0_exact {sevm : Sevm} {base : Devm}
    {memory : Mem} {gas c : Nat} {index count head tail packed : B256} {out : Outcome}
    (charge : gVerylow +
      (calculateMemoryGasCost (memExtSize memory.size (systemRecordAmountOffset index).toNat 1)
        - calculateMemoryGasCost memory.size) = c)
    (next : SFunc.RunExact prog sevm
      (St base [1 + index, count, head, tail]
        (memory.write (systemRecordAmountOffset index).toNat [(packed >>> 64).2.2.toUInt8]) gas)
      t_00e1_c6 out) :
    SFunc.RunExact prog sevm
      (St base [systemRecordAmountOffset index, packed >>> 64, index, count, head, tail]
        memory (gas + 17 + c)) systemBodyByte0Tree out := by
  have gasEq : gas + 17 + c = gas + 8 + 3 + 3 + 3 + c := by omega
  rw [gasEq]
  unfold systemBodyByte0Tree
  apply rx_mstore8 (Devm.extCost_add_of_size rfl charge) rfl
  apply rx_push rfl (by change 4 < 1024; decide)
  apply rx_add' (v := 1 + index) rfl (by change 3 < 1024; decide)
  apply rx_push rfl (by change 4 < 1024; decide)
  exact rx_jump systemBody_loop_lookup next

/-- A next-header continuation constructs the actual amount suffix with exact gas. -/
theorem systemBody_amount_exact {sevm : Sevm} {base : Devm} {memory : Mem} {gas : Nat}
    {index count head tail packed : B256} {out : Outcome}
    (next : SFunc.RunExact prog sevm
      (St base [1 + index, count, head, tail]
        ((systemRecordAmountStage index packed).applyMemory memory) gas) t_00e1_c6 out) :
    SFunc.RunExact prog sevm
      (St base [packed, systemRecordSuffixOffset index, index, count, head, tail]
        memory (gas + systemBodyAmountGas index packed memory)) systemBodyAmountTree out := by
  simp only [systemRecordAmountStage, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil] at next
  let m1 : Mem := memory.write (7 + systemRecordAmountOffset index).toNat
    [((packed >>> 64) >>> 56).2.2.toUInt8]
  let m2 : Mem := m1.write (6 + systemRecordAmountOffset index).toNat
    [((packed >>> 64) >>> 48).2.2.toUInt8]
  let m3 : Mem := m2.write (5 + systemRecordAmountOffset index).toNat
    [((packed >>> 64) >>> 40).2.2.toUInt8]
  let m4 : Mem := m3.write (4 + systemRecordAmountOffset index).toNat
    [((packed >>> 64) >>> 32).2.2.toUInt8]
  let m5 : Mem := m4.write (3 + systemRecordAmountOffset index).toNat
    [((packed >>> 64) >>> 24).2.2.toUInt8]
  let m6 : Mem := m5.write (2 + systemRecordAmountOffset index).toNat
    [((packed >>> 64) >>> 16).2.2.toUInt8]
  let m7 : Mem := m6.write (1 + systemRecordAmountOffset index).toNat
    [((packed >>> 64) >>> 8).2.2.toUInt8]
  have tail := systemBody_byte0_exact (packed := packed)
    (memory := m7)
    (c := systemRecordAmountCharge index packed memory 7)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) next
  have tail := systemBody_byte1_exact (packed := packed)
    (memory := m6)
    (c := systemRecordAmountCharge index packed memory 6)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) tail
  have tail := systemBody_byte2_exact (packed := packed)
    (memory := m5)
    (c := systemRecordAmountCharge index packed memory 5)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) tail
  have tail := systemBody_byte3_exact (packed := packed)
    (memory := m4)
    (c := systemRecordAmountCharge index packed memory 4)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) tail
  have tail := systemBody_byte4_exact (packed := packed)
    (memory := m3)
    (c := systemRecordAmountCharge index packed memory 3)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) tail
  have tail := systemBody_byte5_exact (packed := packed)
    (memory := m2)
    (c := systemRecordAmountCharge index packed memory 2)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) tail
  have tail := systemBody_byte6_exact (packed := packed)
    (memory := m1)
    (c := systemRecordAmountCharge index packed memory 1)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_succ, List.getElem?_cons_zero, List.length_cons, List.length_nil, List.take_succ_cons, List.take_zero, MemoryStage.applyMemory_cons, MemoryStage.applyMemory_nil]; rfl) tail
  have tail := systemBody_byte7_exact (packed := packed)
    (memory := memory)
    (c := systemRecordAmountCharge index packed memory 0)
    (by simp only [systemRecordAmountCharge, systemRecordAmountStage, List.getElem?_cons_zero,
      List.length_cons, List.length_nil, List.take_zero, MemoryStage.applyMemory_nil]) tail
  have ready := systemBody_amount_prep_exact (packed := packed) tail
  have gasEq : gas + systemBodyAmountGas index packed memory =
      gas + 17 + systemRecordAmountCharge index packed memory 7
      + systemRecordAmountCharge index packed memory 6 + 18
      + systemRecordAmountCharge index packed memory 5 + 18
      + systemRecordAmountCharge index packed memory 4 + 18
      + systemRecordAmountCharge index packed memory 3 + 18
      + systemRecordAmountCharge index packed memory 2 + 18
      + systemRecordAmountCharge index packed memory 1 + 18
      + systemRecordAmountCharge index packed memory 0 + 18 + 21 := by
    unfold systemBodyAmountGas
    simp only [gVerylow, gMid]
    omega
  rw [gasEq]
  exact ready

end Blanc.Lift.WithdrawalRequest
