import Blanc.Lift.UniswapV2Pair.TransferFromCore
import Blanc.Lift.UniswapV2Pair.TransferEntries

/-! Literal transferFrom decoder, selected allowance branch and pc-zero route. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def transferFromOwner (sevm : Sevm) : Adr := (Sevm.dataWord sevm 4).toAdr
def transferFromRecipient (sevm : Sevm) : Adr := (Sevm.dataWord sevm 36).toAdr
def transferFromAmount (sevm : Sevm) : B256 := Sevm.dataWord sevm 68
abbrev transferFromMaximal (sevm : Sevm) (b : Devm) : Prop :=
  transferFromAllowanceWord sevm b (transferFromOwner sevm) = B256.max

def transferFromFirst (sevm : Sevm) (b : Devm) : Devm :=
  transferFromFirstBase sevm b (transferFromOwner sevm)
def transferFromSecond (sevm : Sevm) (b : Devm) : Devm :=
  transferFromSecondBase sevm (transferFromFirst sevm b) (transferFromOwner sevm)
def transferFromReduced (sevm : Sevm) (b : Devm) : B256 :=
  transferFromAllowanceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) - transferFromAmount sevm
def transferFromStored (sevm : Sevm) (b : Devm) : Devm :=
  transferFromStoreBase sevm (transferFromSecond sevm b) (transferFromOwner sevm) (transferFromReduced sevm b)
def transferFromBalanceBase (sevm : Sevm) (b : Devm) : Devm :=
  if transferFromMaximal sevm b then transferFromFirst sevm b else transferFromStored sevm b
def transferFromBalanceMemory (sevm : Sevm) (b : Devm) (M : Mem) : Mem :=
  let m := approveScratch M (transferFromOwner sevm).toB256 sevm.caller.toB256
  if transferFromMaximal sevm b then m else
    approveScratch (approveScratch m (transferFromOwner sevm).toB256 sevm.caller.toB256)
      (transferFromOwner sevm).toB256 sevm.caller.toB256
def transferFromDebitWord (sevm : Sevm) (b : Devm) : B256 :=
  transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) - transferFromAmount sevm
def transferFromLoaded (sevm : Sevm) (b : Devm) : Devm :=
  afterSload sevm (transferFromBalanceBase sevm b) (transferBalanceSlot (transferFromOwner sevm))
def transferFromDebited (sevm : Sevm) (b : Devm) : Devm :=
  transferDebitBase sevm (transferFromLoaded sevm b) (transferFromOwner sevm) (transferFromDebitWord sevm b)
def transferFromCreditWord (sevm : Sevm) (b : Devm) : B256 :=
  transferRecipientWord sevm (transferFromLoaded sevm b) (transferFromOwner sevm)
    (transferFromRecipient sevm) (transferFromDebitWord sevm b)

def transferFromFirstCharge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm b (transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller)
def transferFromSecondCharge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm (transferFromFirst sevm b) (transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller)
def transferFromAllowanceCharge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (transferFromSecond sevm b)
    (transferFromAllowanceSlot (transferFromOwner sevm) sevm.caller) (transferFromReduced sevm b)
def transferFromSourceCharge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm (transferFromBalanceBase sevm b) (transferBalanceSlot (transferFromOwner sevm))
def transferFromDebitCharge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (transferFromLoaded sevm b) (transferBalanceSlot (transferFromOwner sevm)) (transferFromDebitWord sevm b)
def transferFromRecipientCharge (sevm : Sevm) (b : Devm) : Nat :=
  sloadCost sevm (transferFromDebited sevm b) (transferBalanceSlot (transferFromRecipient sevm))
def transferFromCreditCharge (sevm : Sevm) (b : Devm) : Nat :=
  sstoreCost sevm (afterSload sevm (transferFromDebited sevm b) (transferBalanceSlot (transferFromRecipient sevm)))
    (transferBalanceSlot (transferFromRecipient sevm)) (transferFromCreditWord sevm b + transferFromAmount sevm)
def transferFromCreditSafe (sevm : Sevm) (b : Devm) : Prop :=
  (transferFromCreditWord sevm b).toNat + (transferFromAmount sevm).toNat < 2 ^ 256
def transferFromAllowanceSafe (sevm : Sevm) (b : Devm) : Prop :=
  transferFromMaximal sevm b ∨
    transferFromAmount sevm ≤ transferFromAllowanceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm)

def transferFromRawPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  St (transferCoreBase sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm)
    (transferFromRecipient sevm) (transferFromAmount sevm)) (1 :: R)
    (transferCoreMemory (transferFromBalanceMemory sevm b M) (transferFromOwner sevm)
      (transferFromRecipient sevm) (transferFromAmount sevm)) G
def transferFromPublicPost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (G : Nat) : Devm :=
  getterWordPost (transferCoreBase sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm)
    (transferFromRecipient sevm) (transferFromAmount sevm)) R
    (transferCoreMemory (transferFromBalanceMemory sevm b M) (transferFromOwner sevm)
      (transferFromRecipient sevm) (transferFromAmount sevm)) 1 G

theorem transferFromBalanceMemory_ptr {sevm : Sevm} {b : Devm} {M : Mem}
    (mem : PtrMem 128 96 M) : PtrMem 128 96 (transferFromBalanceMemory sevm b M) := by
  have m := approveScratch_ptr mem (transferFromOwner sevm).toB256 sevm.caller.toB256
  unfold transferFromBalanceMemory
  split
  · exact m
  · exact approveScratch_ptr (approveScratch_ptr m (transferFromOwner sevm).toB256 sevm.caller.toB256)
      (transferFromOwner sevm).toB256 sevm.caller.toB256

theorem transferFromRawMemory_ptr {sevm : Sevm} {b : Devm} {M : Mem}
    (mem : PtrMem 128 96 M) :
    PtrMem 128 160 (transferCoreMemory (transferFromBalanceMemory sevm b M)
      (transferFromOwner sevm) (transferFromRecipient sevm) (transferFromAmount sevm)) := by
  exact transferCoreMemory_ptr (transferFromBalanceMemory_ptr mem)

theorem transferFrom48_selected_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm
      (St b (transferFromAmount sevm :: (transferFromRecipient sevm).toB256 ::
        (transferFromOwner sevm).toB256 :: ρ :: R) M G) t_0e1e_c48 o) :
    transferFromAllowanceSafe sevm b ∧
      transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) ∧
      sevm.isStatic = false ∧ transferFromCreditSafe sevm b ∧
      ∃ residual, o = .returned (transferFromRawPost sevm b R M residual) := by
  rcases transferFrom48_inv fork mem run with maximal | finite
  · obtain ⟨same, cover, nonstatic, nowrap, residual, result⟩ := maximal
    refine ⟨.inl same, ?_, nonstatic, ?_, residual, ?_⟩
    · simpa only [transferFromBalanceBase, ite_eq_left same, transferFromFirst] using cover
    · simpa only [transferFromCreditSafe, transferFromCreditWord, transferFromLoaded,
        transferFromDebitWord, transferFromBalanceBase, ite_eq_left same, transferFromFirst] using nowrap
    · simpa only [transferFromRawPost, transferFromBalanceBase, transferFromBalanceMemory,
        ite_eq_left same, transferFromFirst, transferFromJoinPost] using result
  · obtain ⟨different, allowed, cover, nonstatic, nowrap, residual, result⟩ := finite
    refine ⟨.inr allowed, ?_, nonstatic, ?_, residual, ?_⟩
    · simpa only [transferFromBalanceBase, ite_eq_right different, transferFromStored,
        transferFromSecond, transferFromFirst, transferFromReduced] using cover
    · simpa only [transferFromCreditSafe, transferFromCreditWord, transferFromLoaded,
        transferFromDebitWord, transferFromBalanceBase, ite_eq_right different, transferFromStored,
        transferFromSecond, transferFromFirst, transferFromReduced] using nowrap
    · simpa only [transferFromRawPost, transferFromBalanceBase, transferFromBalanceMemory,
        ite_eq_right different, transferFromStored, transferFromSecond, transferFromFirst,
        transferFromReduced, transferFromFirstCharge, transferFromSecondCharge, transferFromAllowanceCharge,
      transferFromFinitePost, transferFromStorePost, transferFromJoinPost] using result


def transferFromCoreGas (sevm : Sevm) (b : Devm) : Nat :=
  transferFromFirstCharge sevm b + transferFromSourceCharge sevm b + transferFromDebitCharge sevm b +
    transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b +
    if transferFromMaximal sevm b then 2551 else
      transferFromSecondCharge sevm b + transferFromAllowanceCharge sevm b + 2930

theorem transferFrom48_selected_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (allowed : transferFromAllowanceSafe sevm b)
    (allowanceSentry : ¬ transferFromMaximal sevm b →
      gCallStipend < G + transferFromAllowanceCharge sevm b + transferFromSourceCharge sevm b +
        transferFromDebitCharge sevm b + transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2382)
    (debitSentry : gCallStipend < G + transferFromDebitCharge sevm b +
      transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2105)
    (creditSentry : gCallStipend < G + transferFromCreditCharge sevm b + 1865)
    (nonstatic : sevm.isStatic = false)
    (cover : transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm))
    (nowrap : transferFromCreditSafe sevm b) (room : R.length ≤ 1008) :
    SFunc.RunExact cert.prog sevm
      (St b (transferFromAmount sevm :: (transferFromRecipient sevm).toB256 ::
        (transferFromOwner sevm).toB256 :: ρ :: R) M (G + transferFromCoreGas sevm b)) t_0e1e_c48
      (.returned (transferFromRawPost sevm b R M G)) := by
  by_cases maximal : transferFromMaximal sevm b
  · have sourceEq : transferFromSourceCharge sevm b =
        sloadCost sevm (transferFromFirst sevm b) (transferBalanceSlot (transferFromOwner sevm)) := by
      rw [transferFromSourceCharge, transferFromBalanceBase, ite_eq_left maximal]
    have debitEq : transferFromDebitCharge sevm b =
        sstoreCost sevm (afterSload sevm (transferFromFirst sevm b) (transferBalanceSlot (transferFromOwner sevm)))
          (transferBalanceSlot (transferFromOwner sevm))
          (transferSourceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) - transferFromAmount sevm) := by
      simp only [transferFromDebitCharge, transferFromLoaded, transferFromDebitWord,
        transferFromBalanceBase, ite_eq_left maximal]
    have loadEq : transferFromRecipientCharge sevm b =
        sloadCost sevm (transferDebitBase sevm
          (afterSload sevm (transferFromFirst sevm b) (transferBalanceSlot (transferFromOwner sevm)))
          (transferFromOwner sevm)
          (transferSourceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) - transferFromAmount sevm))
          (transferBalanceSlot (transferFromRecipient sevm)) := by
      simp only [transferFromRecipientCharge, transferFromDebited, transferFromLoaded,
        transferFromDebitWord, transferFromBalanceBase, ite_eq_left maximal]
    have creditEq : transferFromCreditCharge sevm b =
        sstoreCost sevm (afterSload sevm (transferDebitBase sevm
          (afterSload sevm (transferFromFirst sevm b) (transferBalanceSlot (transferFromOwner sevm)))
          (transferFromOwner sevm)
          (transferSourceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) - transferFromAmount sevm))
          (transferBalanceSlot (transferFromRecipient sevm))) (transferBalanceSlot (transferFromRecipient sevm))
          (transferRecipientWord sevm
            (afterSload sevm (transferFromFirst sevm b) (transferBalanceSlot (transferFromOwner sevm)))
            (transferFromOwner sevm) (transferFromRecipient sevm)
            (transferSourceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) - transferFromAmount sevm) + transferFromAmount sevm) := by
      simp only [transferFromCreditCharge, transferFromDebited, transferFromLoaded, transferFromCreditWord,
        transferFromDebitWord, transferFromBalanceBase, ite_eq_left maximal]
    have covered := cover
    have safe := nowrap
    simp only [transferFromBalanceBase, ite_eq_left maximal, transferFromFirst] at covered
    simp only [transferFromCreditSafe, transferFromCreditWord, transferFromLoaded,
      transferFromDebitWord, transferFromBalanceBase, ite_eq_left maximal, transferFromFirst] at safe
    have result := transferFrom48_max_exact (ρ := ρ) fork mem rfl maximal sourceEq debitEq loadEq creditEq
      debitSentry creditSentry nonstatic covered safe room
    have gas : G + transferFromCoreGas sevm b =
        G + transferFromFirstCharge sevm b + transferFromSourceCharge sevm b + transferFromDebitCharge sevm b +
          transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2551 := by
      simp only [transferFromCoreGas, ite_eq_left maximal]
      omega
    rw [gas]
    simpa only [transferFromRawPost, transferFromBalanceBase, transferFromBalanceMemory,
      ite_eq_left maximal, transferFromFirst, transferFromFirstCharge, transferFromJoinPost] using result
  · have permitted : transferFromAmount sevm ≤
        transferFromAllowanceWord sevm (transferFromFirst sevm b) (transferFromOwner sevm) :=
      allowed.resolve_left maximal
    have sourceEq : transferFromSourceCharge sevm b =
        sloadCost sevm (transferFromStored sevm b) (transferBalanceSlot (transferFromOwner sevm)) := by
      rw [transferFromSourceCharge, transferFromBalanceBase, ite_eq_right maximal]
    have debitEq : transferFromDebitCharge sevm b =
        sstoreCost sevm (afterSload sevm (transferFromStored sevm b) (transferBalanceSlot (transferFromOwner sevm)))
          (transferBalanceSlot (transferFromOwner sevm))
          (transferSourceWord sevm (transferFromStored sevm b) (transferFromOwner sevm) - transferFromAmount sevm) := by
      simp only [transferFromDebitCharge, transferFromLoaded, transferFromDebitWord,
        transferFromBalanceBase, ite_eq_right maximal]
    have loadEq : transferFromRecipientCharge sevm b =
        sloadCost sevm (transferDebitBase sevm
          (afterSload sevm (transferFromStored sevm b) (transferBalanceSlot (transferFromOwner sevm)))
          (transferFromOwner sevm)
          (transferSourceWord sevm (transferFromStored sevm b) (transferFromOwner sevm) - transferFromAmount sevm))
          (transferBalanceSlot (transferFromRecipient sevm)) := by
      simp only [transferFromRecipientCharge, transferFromDebited, transferFromLoaded,
        transferFromDebitWord, transferFromBalanceBase, ite_eq_right maximal]
    have creditEq : transferFromCreditCharge sevm b =
        sstoreCost sevm (afterSload sevm (transferDebitBase sevm
          (afterSload sevm (transferFromStored sevm b) (transferBalanceSlot (transferFromOwner sevm)))
          (transferFromOwner sevm)
          (transferSourceWord sevm (transferFromStored sevm b) (transferFromOwner sevm) - transferFromAmount sevm))
          (transferBalanceSlot (transferFromRecipient sevm))) (transferBalanceSlot (transferFromRecipient sevm))
          (transferRecipientWord sevm
            (afterSload sevm (transferFromStored sevm b) (transferBalanceSlot (transferFromOwner sevm)))
            (transferFromOwner sevm) (transferFromRecipient sevm)
            (transferSourceWord sevm (transferFromStored sevm b) (transferFromOwner sevm) - transferFromAmount sevm) + transferFromAmount sevm) := by
      simp only [transferFromCreditCharge, transferFromDebited, transferFromLoaded, transferFromCreditWord,
        transferFromDebitWord, transferFromBalanceBase, ite_eq_right maximal]
    have covered := cover
    have safe := nowrap
    simp only [transferFromBalanceBase, ite_eq_right maximal, transferFromStored,
      transferFromSecond, transferFromFirst, transferFromReduced] at covered
    simp only [transferFromCreditSafe, transferFromCreditWord, transferFromLoaded,
      transferFromDebitWord, transferFromBalanceBase, ite_eq_right maximal, transferFromStored,
      transferFromSecond, transferFromFirst, transferFromReduced] at safe
    have result := transferFrom48_finite_exact (ρ := ρ) fork mem rfl maximal rfl permitted rfl
      (allowanceSentry maximal) sourceEq debitEq loadEq creditEq debitSentry creditSentry nonstatic covered safe room
    have gas : G + transferFromCoreGas sevm b =
        G + transferFromFirstCharge sevm b + transferFromSecondCharge sevm b + transferFromAllowanceCharge sevm b +
          transferFromSourceCharge sevm b + transferFromDebitCharge sevm b +
          transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2930 := by
      simp only [transferFromCoreGas, ite_eq_right maximal]
      omega
    rw [gas]
    simpa only [transferFromRawPost, transferFromBalanceBase, transferFromBalanceMemory,
      ite_eq_right maximal, transferFromStored, transferFromSecond, transferFromFirst,
      transferFromReduced, transferFromFirstCharge, transferFromSecondCharge, transferFromAllowanceCharge,
      transferFromFinitePost, transferFromStorePost, transferFromJoinPost] using result


theorem transferFrom_decoder_exact {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (allowed : transferFromAllowanceSafe sevm b)
    (allowanceSentry : ¬ transferFromMaximal sevm b →
      gCallStipend < G + transferFromAllowanceCharge sevm b + transferFromSourceCharge sevm b +
        transferFromDebitCharge sevm b + transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2431)
    (debitSentry : gCallStipend < G + transferFromDebitCharge sevm b +
      transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2154)
    (creditSentry : gCallStipend < G + transferFromCreditCharge sevm b + 1914)
    (nonstatic : sevm.isStatic = false)
    (cover : transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm))
    (nowrap : transferFromCreditSafe sevm b) :
    SFunc.RunExact cert.prog sevm (St b [avail, 4, 0x034e, sel] M
      (G + transferFromCoreGas sevm b + 114)) t_03c3_c93
      (.halted (transferFromPublicPost sevm b [sel] M G)) := by
  have outmem := transferFromRawMemory_ptr (sevm := sevm) (b := b) mem
  unfold t_03c3_c93
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := ~~~ addressMask) (by decide)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_and (v := (transferFromOwner sevm).toB256)
    (by exact addressSlotReadWord_eq_toAdr_toB256 _)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap2 ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_add' (v := 36) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_and (v := (transferFromRecipient sevm).toB256)
    (by exact addressSlotReadWord_eq_toAdr_toB256 _)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_swap1 ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_add' (v := 68) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldataload (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0e1e) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  have gas : G + transferFromCoreGas sevm b + 57 = ((G + 49) + transferFromCoreGas sevm b) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_0e1e_c48) rfl
    (transferFrom48_selected_exact fork mem allowed
      (fun finite => by have sentry := allowanceSentry finite; omega)
      (by omega) (by omega) nonstatic cover nowrap
      (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact writerBool_tail_exact outmem (by simp only [List.length_cons, List.length_nil]; decide)

theorem transferFrom_decoder_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel avail : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [avail, 4, 0x034e, sel] M G) t_03c3_c93 o) :
    transferFromAllowanceSafe sevm b ∧
      transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) ∧
      sevm.isStatic = false ∧ transferFromCreditSafe sevm b ∧
      ∃ residual, o = .halted (transferFromPublicPost sevm b [sel] M residual) := by
  have outmem := transferFromRawMemory_ptr (sevm := sevm) (b := b) mem
  have h := run.cut
  unfold t_03c3_c93 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := (transferFromOwner sevm).toB256)
    (by exact ff20_and_word _) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 36) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := (transferFromRecipient sevm).toB256)
    (by exact ff20_and_word _) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 68) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, call⟩ := ric_call (g := t_0e1e_c48) rfl h
  rcases call with ⟨d, core, tail⟩ | ⟨d, core, _⟩
  · obtain ⟨allowed, cover, nonstatic, nowrap, _, eq⟩ := transferFrom48_selected_inv fork mem core
    cases eq
    obtain ⟨residual, result⟩ := writerBool_tail_inv outmem tail.uncut
    exact ⟨allowed, cover, nonstatic, nowrap, residual, result⟩
  · obtain ⟨_, _, _, _, _, eq⟩ := transferFrom48_selected_inv fork mem core
    cases eq


theorem transferFrom_entry_exact {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (guard : (96 : B256) ≤ sevm.data.length.toB256 - 4)
    (allowed : transferFromAllowanceSafe sevm b)
    (allowanceSentry : ¬ transferFromMaximal sevm b →
      gCallStipend < G + transferFromAllowanceCharge sevm b + transferFromSourceCharge sevm b +
        transferFromDebitCharge sevm b + transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2431)
    (debitSentry : gCallStipend < G + transferFromDebitCharge sevm b +
      transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2154)
    (creditSentry : gCallStipend < G + transferFromCreditCharge sevm b + 1914)
    (nonstatic : sevm.isStatic = false)
    (cover : transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm))
    (nowrap : transferFromCreditSafe sevm b) :
    SFunc.RunExact cert.prog sevm (St b [sel] M
      (G + transferFromCoreGas sevm b + 154)) t_03ad_c93
      (.halted (transferFromPublicPost sevm b [sel] M G)) := by
  unfold t_03ad_c93
  refine rx_dest ?_
  refine rx_push (w := 0x034e) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 4) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_sub' (v := sevm.data.length.toB256 - 4) rfl
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 96) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_dup2 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le guard)
    (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x03c3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  exact transferFrom_decoder_exact fork mem allowed allowanceSentry debitSentry creditSentry nonstatic cover nowrap

theorem transferFrom_entry_inv {sevm : Sevm} {b : Devm} {M : Mem}
    {G : Nat} {sel : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_03ad_c93 o) :
    (96 : B256) ≤ sevm.data.length.toB256 - 4 ∧ transferFromAllowanceSafe sevm b ∧
      transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) ∧
      sevm.isStatic = false ∧ transferFromCreditSafe sevm b ∧
      ∃ residual, o = .halted (transferFromPublicPost sevm b [sel] M residual) := by
  have h := run.cut
  unfold t_03ad_c93 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldatasize hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sub hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_lt hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · unfold t_03bf_c93 at bad
    obtain ⟨_, _, bad⟩ := ric_next bad
    obtain ⟨_, _, bad⟩ := ric_next bad
    exact (ric_revert bad).elim
  · simp only [show Bytes.toB256 [4] = (4 : B256) from rfl,
      show Bytes.toB256 [0x60] = (96 : B256) from rfl] at nonzero
    have guard : (96 : B256) ≤ sevm.data.length.toB256 - 4 := by
      by_contra ne
      have flag : B256.ltCheck (sevm.data.length.toB256 - 4) 96 = 1 := by
        simp only [B256.ltCheck, lt_of_not_ge ne, ite_true]
      rw [flag] at nonzero
      exact nonzero (by decide)
    exact ⟨guard, transferFrom_decoder_inv fork mem h.uncut⟩

theorem transferFrom_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (body : SFunc.RunExact cert.prog sevm (St b [0x23b872dd] getterInitMemory G) t_03ad_c93 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 165)) t_0000_c0 o := by
  refine getterString_guards_exact (G := G + 102) value size ?_
  unfold t_001a_c0
  refine rx_push (w := 0) rfl (by decide) ?_
  refine rx_calldataload (by decide) ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_shr (v := 0x23b872dd) selector (by decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00f9_c0
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_0105_c0
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x3644e515) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0140) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0140_c0
  refine rx_dest ?_
  exact cmp_hit (tgt := t_03ad_c93) rfl rfl body

theorem transferFrom_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ residual, SFunc.Run cert.prog sevm (St b [0x23b872dd] M residual) t_03ad_c93 o := by
  have h := run.cut
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x23b872dd : B256) from selector] at hd
  subst d
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x23b872dd : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  unfold t_00f9_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x23b872dd : B256)
    = (0 : B256) from by decide, ite_true] at h
  unfold t_0105_c0 at h
  obtain ⟨_, h⟩ := ric_cmp_gt h
  simp only [show B256.gtCheck (Bytes.toB256 [0x36, 0x44, 0xe5, 0x15]) (0x23b872dd : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  unfold t_0140_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨_, h⟩ := ric_cmp_eq (g := t_03ad_c93) (by intro bad; cases bad) rfl h
  simp only [show B256.eqCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x23b872dd : B256)
    = (1 : B256) from by decide, show (1 : B256) ≠ 0 from by decide, ite_false] at h
  exact ⟨_, h.uncut⟩


def transferFromPublicGas (sevm : Sevm) (b : Devm) : Nat := transferFromCoreGas sevm b + 319

theorem transferFrom_pc0_exact {sevm : Sevm} {b : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (value : sevm.value = 0)
    (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (guard : (96 : B256) ≤ sevm.data.length.toB256 - 4)
    (allowed : transferFromAllowanceSafe sevm b)
    (allowanceSentry : ¬ transferFromMaximal sevm b →
      gCallStipend < G + transferFromAllowanceCharge sevm b + transferFromSourceCharge sevm b +
        transferFromDebitCharge sevm b + transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2431)
    (debitSentry : gCallStipend < G + transferFromDebitCharge sevm b +
      transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2154)
    (creditSentry : gCallStipend < G + transferFromCreditCharge sevm b + 1914)
    (nonstatic : sevm.isStatic = false)
    (cover : transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm))
    (nowrap : transferFromCreditSafe sevm b) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + transferFromPublicGas sevm b))
      (transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  have gas : G + transferFromPublicGas sevm b = (G + transferFromCoreGas sevm b + 154) + 165 := by
    unfold transferFromPublicGas
    omega
  rw [gas]
  exact transferFrom_dispatch_exact value size selector
    (transferFrom_entry_exact fork getterInitMemory_ptr guard allowed allowanceSentry
      debitSentry creditSentry nonstatic cover nowrap)

theorem transferFrom_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (96 : B256) ≤ sevm.data.length.toB256 - 4 ∧ transferFromAllowanceSafe sevm b ∧
      transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) ∧
      sevm.isStatic = false ∧ transferFromCreditSafe sevm b ∧
      ∃ residual, post = transferFromPublicPost sevm b [0x23b872dd] getterInitMemory residual := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := transferFrom_selector_inv selector run
  obtain ⟨guard, allowed, cover, nonstatic, nowrap, residual, result⟩ :=
    transferFrom_entry_inv fork getterInitMemory_ptr run
  exact ⟨value, size, guard, allowed, cover, nonstatic, nowrap, residual, Outcome.halted.inj result⟩

theorem transferFrom_bytecode_refines_raw {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      (96 : B256) ≤ sevm.data.length.toB256 - 4 ∧ transferFromAllowanceSafe sevm b ∧
      transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm) ∧
      sevm.isStatic = false ∧ transferFromCreditSafe sevm b ∧
      ∃ residual, post = transferFromPublicPost sevm b [0x23b872dd] getterInitMemory residual :=
  transferFrom_pc0_inv fork selector (lift_sound cert_check codeEq fork run)

theorem transferFrom_bytecode_live_raw {sevm : Sevm} {b : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (guard : (96 : B256) ≤ sevm.data.length.toB256 - 4)
    (allowed : transferFromAllowanceSafe sevm b)
    (allowanceSentry : ¬ transferFromMaximal sevm b →
      gCallStipend < G + transferFromAllowanceCharge sevm b + transferFromSourceCharge sevm b +
        transferFromDebitCharge sevm b + transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2431)
    (debitSentry : gCallStipend < G + transferFromDebitCharge sevm b +
      transferFromRecipientCharge sevm b + transferFromCreditCharge sevm b + 2154)
    (creditSentry : gCallStipend < G + transferFromCreditCharge sevm b + 1914)
    (nonstatic : sevm.isStatic = false)
    (cover : transferFromAmount sevm ≤ transferSourceWord sevm (transferFromBalanceBase sevm b) (transferFromOwner sevm))
    (nowrap : transferFromCreditSafe sevm b) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + transferFromPublicGas sevm b))
      (.ok (transferFromPublicPost sevm b [0x23b872dd] getterInitMemory G))) :=
  lift_exact cert_check jumps_ok codeEq fork
    (transferFrom_pc0_exact fork value size selector guard allowed allowanceSentry
      debitSentry creditSentry nonstatic cover nowrap)

end Blanc.Lift.UniswapV2Pair
