import Blanc.Lift.UniswapV2Pair.GetterStringWalk

/-! Ten scalar getter paths of the checked Pair runtime. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

inductive ConstantScalar
  | decimals | minimumLiquidity | permitTypehash

def ConstantScalar.value : ConstantScalar → B256
  | .decimals => 18
  | .minimumLiquidity => 1000
  | .permitTypehash => Blanc.Lift.UniswapV2Pair.permitTypehash

def ConstantScalar.head : ConstantScalar → UInt8
  | .decimals => 0x12
  | .minimumLiquidity => 0x03
  | .permitTypehash => 0x6e

def ConstantScalar.tail : ConstantScalar → Bytes
  | .decimals => []
  | .minimumLiquidity => [0xe8]
  | .permitTypehash => [0x71, 0xed, 0xae, 0x12, 0xb1, 0xb9, 0x7f,
      0x4d, 0x1f, 0x60, 0x37, 0x0f, 0xef, 0x10, 0x10, 0x5f, 0xa2, 0xfa, 0xae,
      0x01, 0x26, 0x11, 0x4a, 0x16, 0x9c, 0x64, 0x84, 0x5d, 0x61, 0x26, 0xc9]

def ConstantScalar.bytes (s : ConstantScalar) : Bytes := s.head :: s.tail

theorem ConstantScalar.bytes_bound (s : ConstantScalar) : s.bytes.length ≤ 32 := by
  cases s <;> decide

theorem ConstantScalar.bytes_value (s : ConstantScalar) :
    Bytes.toB256 s.bytes = s.value := by
  cases s <;> rfl

def ConstantScalar.callee : ConstantScalar → SFunc
  | .decimals => t_0f21_c50
  | .minimumLiquidity => t_18d8_c33
  | .permitTypehash => t_0efd_c49

theorem ConstantScalar.callee_shape (s : ConstantScalar) :
    s.callee = .dest (.next (.push s.bytes s.bytes_bound) (.next (.reg (.dup 1)) .ret)) := by
  cases s <;> rfl

theorem constantScalar_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256}
    (s : ConstantScalar) (room : R.length ≤ 1021) :
    SFunc.RunExact fs sevm (St b (ρ :: R) M (G + 15)) s.callee
      (.returned (St b (s.value :: ρ :: R) M G)) := by
  rw [s.callee_shape]
  refine rx_dest ?_
  refine rx_push s.bytes_value (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  exact rx_ret

theorem constantScalar_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome}
    (s : ConstantScalar)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St b (s.value :: ρ :: R) M G') := by
  have h := run.cut
  rw [s.callee_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_push hd
  rw [s.bytes_value] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

inductive StoredScalar
  | domainSeparator | price0CumulativeLast | price1CumulativeLast | kLast

def StoredScalar.slotByte : StoredScalar → UInt8
  | .domainSeparator => 0x03
  | .price0CumulativeLast => 0x09
  | .price1CumulativeLast => 0x0a
  | .kLast => 0x0b

def StoredScalar.slot (s : StoredScalar) : B256 := Bytes.toB256 [s.slotByte]

def StoredScalar.callee : StoredScalar → SFunc
  | .domainSeparator => t_0f26_c44
  | .price0CumulativeLast => t_1005_c46
  | .price1CumulativeLast => t_100b_c47
  | .kLast => t_13dd_c43

theorem StoredScalar.callee_shape (s : StoredScalar) :
    s.callee = .dest (.next (.push [s.slotByte] (by simp only [List.length_cons, List.length_nil]; decide))
      (.next (.reg .sload) (.next (.reg (.dup 1)) .ret))) := by
  cases s <;> rfl

theorem storedScalar_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {ρ : B256} (s : StoredScalar)
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b s.slot)
    (room : R.length ≤ 1021) :
    SFunc.RunExact fs sevm (St b (ρ :: R) M (G + c + 15)) s.callee
      (.returned (St (afterSload sevm b s.slot)
        (b.getStorVal sevm.currentTarget s.slot :: ρ :: R) M G)) := by
  rw [s.callee_shape]
  refine rx_dest ?_
  refine rx_push (w := s.slot) rfl (by simp only [List.length_cons]; omega) ?_
  have gas : G + c + 11 = (G + 11) + c := by omega
  rw [gas]
  refine rx_sload_selC fork cost (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  exact rx_ret

theorem storedScalar_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome} (s : StoredScalar)
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St (afterSload sevm b s.slot)
      (b.getStorVal sevm.currentTarget s.slot :: ρ :: R) M G') := by
  have h := run.cut
  rw [s.callee_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

inductive AddressScalar
  | factory | token0 | token1

def AddressScalar.slotByte : AddressScalar → UInt8
  | .factory => 0x05
  | .token0 => 0x06
  | .token1 => 0x07

def AddressScalar.slot (s : AddressScalar) : B256 := Bytes.toB256 [s.slotByte]

def AddressScalar.callee : AddressScalar → SFunc
  | .factory => t_1ad4_c35
  | .token0 => t_0dfc_c52
  | .token1 => t_1af0_c28

theorem AddressScalar.callee_shape (s : AddressScalar) :
    s.callee = .dest (.next (.push [s.slotByte] (by simp only [List.length_cons, List.length_nil]; decide))
      (.next (.reg .sload) (.next (.push (List.replicate 20 0xff) (by decide))
      (.next (.reg .and) (.next (.reg (.dup 1)) .ret))))) := by
  cases s <;> rfl

theorem addressScalar_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {ρ : B256} (s : AddressScalar)
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b s.slot)
    (room : R.length ≤ 1020) :
    SFunc.RunExact fs sevm (St b (ρ :: R) M (G + c + 21)) s.callee
      (.returned (St (afterSload sevm b s.slot)
        ((b.getStorVal sevm.currentTarget s.slot).toAdr.toB256 :: ρ :: R) M G)) := by
  rw [s.callee_shape]
  refine rx_dest ?_
  refine rx_push (w := s.slot) rfl (by simp only [List.length_cons]; omega) ?_
  have gas : G + c + 17 = (G + 17) + c := by omega
  rw [gas]
  refine rx_sload_selC fork cost (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := ~~~ addressMask) (by decide)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_and (addressSlotReadWord_eq_toAdr_toB256 _) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  exact rx_ret

theorem addressScalar_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome} (s : AddressScalar)
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) s.callee o) :
    ∃ G', o = .returned (St (afterSload sevm b s.slot)
      ((b.getStorVal sevm.currentTarget s.slot).toAdr.toB256 :: ρ :: R) M G') := by
  have h := run.cut
  rw [s.callee_shape] at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  change d = St (afterSload sevm b s.slot)
    ((Bytes.toB256 (List.replicate 20 0xff) &&& b.getStorVal sevm.currentTarget s.slot) :: ρ :: R) M _ at hd
  rw [show Bytes.toB256 (List.replicate 20 0xff) = ~~~ addressMask from by decide,
    show ((~~~ addressMask) &&& b.getStorVal sevm.currentTarget s.slot) =
      (b.getStorVal sevm.currentTarget s.slot).toAdr.toB256 from addressSlotReadWord_eq_toAdr_toB256 _] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

inductive ScalarGetter
  | constant (s : ConstantScalar)
  | stored (s : StoredScalar)
  | address (s : AddressScalar)

def ScalarGetter.entry : ScalarGetter → Entry
  | .constant .decimals => .decimals
  | .constant .minimumLiquidity => .minimumLiquidity
  | .constant .permitTypehash => .permitTypehash
  | .stored .domainSeparator => .domainSeparator
  | .stored .price0CumulativeLast => .price0CumulativeLast
  | .stored .price1CumulativeLast => .price1CumulativeLast
  | .stored .kLast => .kLast
  | .address .factory => .factory
  | .address .token0 => .token0
  | .address .token1 => .token1

def ScalarGetter.selector : ScalarGetter → B256
  | .constant .decimals => 0x313ce567
  | .constant .minimumLiquidity => 0xba9a7a56
  | .constant .permitTypehash => 0x30adf81f
  | .stored .domainSeparator => 0x3644e515
  | .stored .price0CumulativeLast => 0x5909c0d5
  | .stored .price1CumulativeLast => 0x5a3d5493
  | .stored .kLast => 0x7464fc3d
  | .address .factory => 0xc45a0155
  | .address .token0 => 0xdfe1681
  | .address .token1 => 0xd21220a7

def ScalarGetter.entryTree : ScalarGetter → SFunc
  | .constant .decimals => t_03f8_c95
  | .constant .minimumLiquidity => t_0597_c79
  | .constant .permitTypehash => t_03f0_c94
  | .stored .domainSeparator => t_0416_c89
  | .stored .price0CumulativeLast => t_0459_c91
  | .stored .price1CumulativeLast => t_0461_c92
  | .stored .kLast => t_04cf_c88
  | .address .factory => t_05d2_c81
  | .address .token0 => t_0362_c97
  | .address .token1 => t_05da_c75

def ScalarGetter.calleeIndex : ScalarGetter → Nat
  | .constant .decimals => 50
  | .constant .minimumLiquidity => 33
  | .constant .permitTypehash => 49
  | .stored .domainSeparator => 44
  | .stored .price0CumulativeLast => 46
  | .stored .price1CumulativeLast => 47
  | .stored .kLast => 43
  | .address .factory => 35
  | .address .token0 => 52
  | .address .token1 => 28

def ScalarGetter.calleeHi : ScalarGetter → UInt8
  | .constant .decimals => 0xf
  | .constant .minimumLiquidity => 0x18
  | .constant .permitTypehash => 0xe
  | .stored .domainSeparator => 0xf
  | .stored .price0CumulativeLast => 0x10
  | .stored .price1CumulativeLast => 0x10
  | .stored .kLast => 0x13
  | .address .factory => 0x1a
  | .address .token0 => 0xd
  | .address .token1 => 0x1a

def ScalarGetter.calleeLo : ScalarGetter → UInt8
  | .constant .decimals => 0x21
  | .constant .minimumLiquidity => 0xd8
  | .constant .permitTypehash => 0xfd
  | .stored .domainSeparator => 0x26
  | .stored .price0CumulativeLast => 0x5
  | .stored .price1CumulativeLast => 0xb
  | .stored .kLast => 0xdd
  | .address .factory => 0xd4
  | .address .token0 => 0xfc
  | .address .token1 => 0xf0

def ScalarGetter.tagHi : ScalarGetter → UInt8
  | .constant .decimals => 0x4
  | .constant .minimumLiquidity => 0x3
  | .constant .permitTypehash => 0x3
  | .stored .domainSeparator => 0x3
  | .stored .price0CumulativeLast => 0x3
  | .stored .price1CumulativeLast => 0x3
  | .stored .kLast => 0x3
  | .address .factory => 0x3
  | .address .token0 => 0x3
  | .address .token1 => 0x3

def ScalarGetter.tagLo : ScalarGetter → UInt8
  | .constant .decimals => 0x0
  | .constant .minimumLiquidity => 0x9b
  | .constant .permitTypehash => 0x9b
  | .stored .domainSeparator => 0x9b
  | .stored .price0CumulativeLast => 0x9b
  | .stored .price1CumulativeLast => 0x9b
  | .stored .kLast => 0x9b
  | .address .factory => 0x6a
  | .address .token0 => 0x6a
  | .address .token1 => 0x6a

def ScalarGetter.dispatchGas : ScalarGetter → Nat
  | .constant .decimals => 209
  | .constant .minimumLiquidity => 164
  | .constant .permitTypehash => 187
  | .stored .domainSeparator => 164
  | .stored .price0CumulativeLast => 208
  | .stored .price1CumulativeLast => 230
  | .stored .kLast => 209
  | .address .factory => 208
  | .address .token0 => 187
  | .address .token1 => 163

def ScalarGetter.callee : ScalarGetter → SFunc
  | .constant s => s.callee
  | .stored s => s.callee
  | .address s => s.callee

def ScalarGetter.tag (s : ScalarGetter) : B256 := Bytes.toB256 [s.tagHi, s.tagLo]

def ScalarGetter.tailTree : ScalarGetter → SFunc
  | .constant .decimals => t_0400_c95
  | .address _ => t_036a_c75
  | _ => t_039b_c98

theorem ScalarGetter.callee_lookup (s : ScalarGetter) :
    cert.prog[s.calleeIndex]? = some s.callee := by
  cases s with
  | constant s => cases s <;> rfl
  | stored s => cases s <;> rfl
  | address s => cases s <;> rfl

theorem ScalarGetter.entry_shape (s : ScalarGetter) :
    s.entryTree = .dest
      (.next (.push [s.tagHi, s.tagLo] (by simp only [List.length_cons, List.length_nil]; decide))
      (.next (.push [s.calleeHi, s.calleeLo] (by simp only [List.length_cons, List.length_nil]; decide))
      (.callNext s.calleeIndex s.tailTree))) := by
  cases s with
  | constant s => cases s <;> rfl
  | stored s => cases s <;> rfl
  | address s => cases s <;> rfl

def ScalarGetter.value (s : ScalarGetter) (sevm : Sevm) (b : Devm) : B256 :=
  match s with
  | .constant s => s.value
  | .stored s => b.getStorVal sevm.currentTarget s.slot
  | .address s => (b.getStorVal sevm.currentTarget s.slot).toAdr.toB256

def ScalarGetter.after (s : ScalarGetter) (sevm : Sevm) (b : Devm) : Devm :=
  match s with
  | .constant _ => b
  | .stored s => afterSload sevm b s.slot
  | .address s => afterSload sevm b s.slot

def ScalarGetter.loadGas (s : ScalarGetter) (sevm : Sevm) (b : Devm) : Nat :=
  match s with
  | .constant _ => 0
  | .stored s => sloadCost sevm b s.slot
  | .address s => sloadCost sevm b s.slot

def ScalarGetter.calleeGas : ScalarGetter → Nat
  | .address _ => 21
  | _ => 15

def ScalarGetter.tailGas : ScalarGetter → Nat
  | .constant .decimals | .address _ => 58
  | _ => 49

def ScalarGetter.entryGas (s : ScalarGetter) : Nat := 15 + s.calleeGas + s.tailGas

def ScalarGetter.SlotMatches (s : ScalarGetter) (st : State) (sevm : Sevm) (b : Devm) : Prop :=
  match s with
  | .constant _ => True
  | .stored .domainSeparator => st.domainSeparator = b.getStorVal sevm.currentTarget 3
  | .stored .price0CumulativeLast => st.price0CumulativeLast = b.getStorVal sevm.currentTarget 9
  | .stored .price1CumulativeLast => st.price1CumulativeLast = b.getStorVal sevm.currentTarget 10
  | .stored .kLast => st.kLast = b.getStorVal sevm.currentTarget 11
  | .address .factory => st.factory = (b.getStorVal sevm.currentTarget 5).toAdr
  | .address .token0 => st.token0 = (b.getStorVal sevm.currentTarget 6).toAdr
  | .address .token1 => st.token1 = (b.getStorVal sevm.currentTarget 7).toAdr

theorem ScalarGetter.source_value {st : State} {sevm : Sevm} {b : Devm}
    (s : ScalarGetter) (slots : s.SlotMatches st sevm b) :
    getterResult st s.entry = some (s.value sevm b).toBytes := by
  cases s with
  | constant s =>
    cases s <;> rfl
  | stored s =>
    cases s <;>
      simp only [ScalarGetter.SlotMatches] at slots <;>
      simp only [ScalarGetter.entry, ScalarGetter.value, StoredScalar.slot,
        StoredScalar.slotByte, getterResult, encodeWords, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, slots] <;> rfl
  | address s =>
    cases s <;>
      simp only [ScalarGetter.SlotMatches] at slots <;>
      simp only [ScalarGetter.entry, ScalarGetter.value, AddressScalar.slot,
        AddressScalar.slotByte, getterResult, encodeWords, List.flatMap_cons,
        List.flatMap_nil, List.append_nil, slots] <;> rfl

theorem ScalarGetter.after_storage (s : ScalarGetter) (sevm : Sevm) (b : Devm) (a : Adr) :
    Devm.getStor (s.after sevm b) a = Devm.getStor b a := by
  cases s with
  | constant _ => rfl
  | stored _ => exact afterSload_getStor _ _ _ _
  | address _ => exact afterSload_getStor _ _ _ _

theorem ScalarGetter.after_logs (s : ScalarGetter) (sevm : Sevm) (b : Devm) :
    (s.after sevm b).logs = b.logs := by
  cases s with
  | constant _ => rfl
  | stored _ => exact afterSload_logs _ _ _
  | address _ => exact afterSload_logs _ _ _

end Blanc.Lift.UniswapV2Pair
