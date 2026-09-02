import Blanc.BeaconDepositAbi
import Blanc.CommonProofs

/-!
# Source-level Beacon deposit ABI inversion

Successful frame proofs run backwards from the actual `Func.Run`.  This
module identifies the values consumed by the ABI validator, proves that every
reverting guard fell through, and retains the exact decoder memory image for
the deposit body.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

private theorem limitGuard_prefix
    {sevm : Sevm} {pre post : Devm} {value : B256} {tail : Stack}
    (hp : value :: tail <<+ pre.stack)
    (run : Line.Run sevm pre
      [dup 0, pushB256 (Nat.toB256 (2 ^ 32)), swap 0, lt, iszero] post) :
    ((value <? Nat.toB256 (2 ^ 32)) =? 0) :: value :: tail <<+
      post.stack := by
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : value :: value :: tail <<+ s1.stack :=
    prefix_of_dup_val q1 (Stack.Nth.head _ _) hp
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  have hp2 : Nat.toB256 (2 ^ 32) :: value :: value :: tail <<+
      s2.stack := prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hswap : Stack.Swap (0 : Fin 16).val
      (Nat.toB256 (2 ^ 32) :: value :: value :: tail)
      (value :: Nat.toB256 (2 ^ 32) :: value :: tail) :=
    Stack.swapCore_zero
  have hp3 : value :: Nat.toB256 (2 ^ 32) :: value :: tail <<+
      s3.stack := Stack.prefix_of_swap hswap (of_run_swap q3) hp2
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  have hp4 : (value <? Nat.toB256 (2 ^ 32)) :: value :: tail <<+
      s4.stack := prefix_of_lt q4 hp3
  rcases Line.of_run_cons run with ⟨_, q5, hnil⟩
  cases hnil
  exact prefix_of_iszero q5 hp4

private theorem endGuard_prefix
    {sevm : Sevm} {pre post : Devm} {offset : B256} {tail : Stack}
    (hp : offset :: tail <<+ pre.stack)
    (run : Line.Run sevm pre
      [dup 0, pushB256 36, add, calldatasize, lt] post) :
    (sevm.data.length.toB256 <? (36 + offset)) :: offset :: tail <<+
      post.stack := by
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : offset :: offset :: tail <<+ s1.stack :=
    prefix_of_dup_val q1 (Stack.Nth.head _ _) hp
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  have hp2 : (36 : B256) :: offset :: offset :: tail <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hp3 : (36 + offset) :: offset :: tail <<+ s3.stack :=
    prefix_of_add q3 hp2
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  have hp4 : sevm.data.length.toB256 :: (36 + offset) :: offset :: tail <<+
      s4.stack := prefix_of_push (of_run_calldatasize q4) hp3
  rcases Line.of_run_cons run with ⟨_, q5, hnil⟩
  cases hnil
  exact prefix_of_lt q5 hp4

private theorem loadLength_prefix
    {sevm : Sevm} {pre post : Devm} {offset : B256} {tail : Stack}
    (hp : offset :: tail <<+ pre.stack)
    (run : Line.Run sevm pre
      [dup 0, pushB256 4, add, calldataload] post) :
    Sevm.dataWord sevm (4 + offset) :: offset :: tail <<+ post.stack := by
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : offset :: offset :: tail <<+ s1.stack :=
    prefix_of_dup_val q1 (Stack.Nth.head _ _) hp
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  have hp2 : (4 : B256) :: offset :: offset :: tail <<+ s2.stack :=
    prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hp3 : (4 + offset) :: offset :: tail <<+ s3.stack :=
    prefix_of_add q3 hp2
  rcases Line.of_run_cons run with ⟨_, q4, hnil⟩
  cases hnil
  exact prefix_of_calldataload_val q4 hp3

private theorem paddedEndGuard_prefix
    {sevm : Sevm} {pre post : Devm}
    {length offset : B256} {tail : Stack}
    (hp : length :: offset :: tail <<+ pre.stack)
    (run : Line.Run sevm pre
      [dup 0, pushB256 31, add, pushB256 31, Ninst.not, Ninst.and,
        dup 2, add, pushB256 36, add, calldatasize, lt] post) :
    (sevm.data.length.toB256 <?
        (36 + (offset + ((~~~ (31 : B256)) &&& (31 + length))))) ::
      length :: offset :: tail <<+ post.stack := by
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : length :: length :: offset :: tail <<+ s1.stack :=
    prefix_of_dup_val q1 (Stack.Nth.head _ _) hp
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  have hp2 : (31 : B256) :: length :: length :: offset :: tail <<+
      s2.stack := prefix_of_push (of_run_pushB256 q2) hp1
  rcases Line.of_run_cons run with ⟨s3, q3, run⟩
  have hp3 : (31 + length) :: length :: offset :: tail <<+ s3.stack :=
    prefix_of_add q3 hp2
  rcases Line.of_run_cons run with ⟨s4, q4, run⟩
  have hp4 : (31 : B256) :: (31 + length) :: length :: offset :: tail <<+
      s4.stack := prefix_of_push (of_run_pushB256 q4) hp3
  rcases Line.of_run_cons run with ⟨s5, q5, run⟩
  have hp5 : (~~~ (31 : B256)) :: (31 + length) :: length :: offset ::
      tail <<+ s5.stack := prefix_of_not q5 hp4
  rcases Line.of_run_cons run with ⟨s6, q6, run⟩
  have hp6 : ((~~~ (31 : B256)) &&& (31 + length)) :: length :: offset ::
      tail <<+ s6.stack := prefix_of_and q6 hp5
  rcases Line.of_run_cons run with ⟨s7, q7, run⟩
  have hp7 : offset :: ((~~~ (31 : B256)) &&& (31 + length)) ::
      length :: offset :: tail <<+ s7.stack :=
    prefix_of_dup_val q7 (by show_nth) hp6
  rcases Line.of_run_cons run with ⟨s8, q8, run⟩
  have hp8 : (offset + ((~~~ (31 : B256)) &&& (31 + length))) ::
      length :: offset :: tail <<+ s8.stack := prefix_of_add q8 hp7
  rcases Line.of_run_cons run with ⟨s9, q9, run⟩
  have hp9 : (36 : B256) ::
      (offset + ((~~~ (31 : B256)) &&& (31 + length))) ::
      length :: offset :: tail <<+ s9.stack :=
    prefix_of_push (of_run_pushB256 q9) hp8
  rcases Line.of_run_cons run with ⟨s10, q10, run⟩
  have hp10 : (36 +
      (offset + ((~~~ (31 : B256)) &&& (31 + length)))) ::
      length :: offset :: tail <<+ s10.stack := prefix_of_add q10 hp9
  rcases Line.of_run_cons run with ⟨s11, q11, run⟩
  have hp11 : sevm.data.length.toB256 ::
      (36 + (offset + ((~~~ (31 : B256)) &&& (31 + length)))) ::
      length :: offset :: tail <<+ s11.stack :=
    prefix_of_push (of_run_calldatasize q11) hp10
  rcases Line.of_run_cons run with ⟨_, q12, hnil⟩
  cases hnil
  exact prefix_of_lt q12 hp11

private theorem accept_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {length offset offsetWord lengthWord : B256} {tail : Stack}
    {body : Func}
    (hp : length :: offset :: tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (mstoreAt lengthWord +++ mstoreAt offsetWord +++ body) post) :
    ∃ next,
      tail <<+ next.stack ∧
      Func.Run fs sevm next body post ∧
      next.memory =
        (pre.memory.write (lengthWord * 32).toNat length.toBytes).write
          (offsetWord * 32).toNat offset.toBytes ∧
      Devm.getStor next = Devm.getStor pre ∧
      Devm.getCode next = Devm.getCode pre := by
  rcases of_run_prepend (mstoreAt lengthWord) _ run with
    ⟨afterLength, lengthRun, run⟩
  rcases of_run_mstoreAt_val lengthRun hp with ⟨hpLength, hmemLength⟩
  rcases of_run_prepend (mstoreAt offsetWord) _ run with
    ⟨next, offsetRun, bodyRun⟩
  rcases of_run_mstoreAt_val offsetRun hpLength with
    ⟨hpNext, hmemOffset⟩
  have hstate : pre.state = next.state :=
    (Line.of_inv Devm.state (by line_inv) lengthRun).trans
      (Line.of_inv Devm.state (by line_inv) offsetRun)
  refine ⟨next, hpNext, bodyRun, ?_, ?_, ?_⟩
  · rw [hmemOffset, hmemLength]
  · funext address
    show (next.state.get address).stor = (pre.state.get address).stor
    rw [← hstate]
  · funext address
    show (next.state.get address).code = (pre.state.get address).code
    rw [← hstate]

/-- A successful post-argument validator walk establishes the exact natural
ABI bounds and reaches its continuation with the decoded offset/length words
stored in the nominated scratch words.  No global calldata-size premise is
needed: the EVM word view of a natural length is its low 256 bits, which are
always bounded above by the original natural length. -/
theorem validateDynamicTailAfterArg_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {head : Nat} {offsetWord lengthWord : B256} {tail : Stack}
    {body : Func}
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hp : depositOffsetWord sevm.data head :: tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (validateDynamicTailAfterArg offsetWord lengthWord body) post) :
    ∃ next,
      DynamicTailDecodable sevm.data head ∧
      tail <<+ next.stack ∧
      Func.Run fs sevm next body post ∧
      next.memory =
        (pre.memory.write (lengthWord * 32).toNat
          (depositLengthWord sevm.data head).toBytes).write
          (offsetWord * 32).toNat
          (depositOffsetWord sevm.data head).toBytes ∧
      Devm.getStor next = Devm.getStor pre ∧
      Devm.getCode next = Devm.getCode pre := by
  let offset := depositOffsetWord sevm.data head
  let length := depositLengthWord sevm.data head
  let rounded : B256 := (~~~ (31 : B256)) &&& (31 + length)
  let paddedEnd : B256 := 36 + (offset + rounded)
  unfold validateDynamicTailAfterArg at run
  rcases of_run_prepend
      [dup 0, pushB256 (Nat.toB256 (2 ^ 32)), swap 0, lt, iszero] _ run with
    ⟨afterOffsetGuard, offsetGuardRun, run⟩
  have hpOffsetGuard :
      ((offset <? Nat.toB256 (2 ^ 32)) =? 0) :: offset :: tail <<+
        afterOffsetGuard.stack :=
    limitGuard_prefix (by simpa only [offset] using hp) offsetGuardRun
  rcases of_run_branch_call_revert hrev run with
    ⟨afterOffset, offsetPop, run⟩
  have hOffsetFlag :
      ((offset <? Nat.toB256 (2 ^ 32)) =? 0) = 0 :=
    (popBurn_pref offsetPop hpOffsetGuard).1.symm
  have hpOffset : offset :: tail <<+ afterOffset.stack :=
    (popBurn_pref offsetPop hpOffsetGuard).2
  have hOffsetWordLt : offset < Nat.toB256 (2 ^ 32) := by
    by_contra hnot
    have hlt : (offset <? Nat.toB256 (2 ^ 32)) = 0 := by
      simp only [B256.ltCheck]
      rw [if_neg hnot]
    rw [hlt] at hOffsetFlag
    exact (by decide +kernel : ((0 : B256) =? 0) ≠ 0) hOffsetFlag
  have hOffset256 : dynamicOffset sevm.data head < 2 ^ 256 :=
    B256.toNat_lt _
  have hOffset : dynamicOffset sevm.data head < 2 ^ 32 := by
    have hnat := B256.toNat_lt_toNat hOffsetWordLt
    rw [depositOffsetWord_toNat hOffset256,
      B256.toNat_toB256_of_lt (by omega)] at hnat
    exact hnat

  rcases of_run_prepend [dup 0, pushB256 36, add, calldatasize, lt] _ run with
    ⟨afterEndGuard, endGuardRun, run⟩
  have hpEndGuard :
      (sevm.data.length.toB256 <? (36 + offset)) :: offset :: tail <<+
        afterEndGuard.stack := endGuard_prefix hpOffset endGuardRun
  rcases of_run_branch_call_revert hrev run with
    ⟨afterEnd, endPop, run⟩
  have hEndFlag : (sevm.data.length.toB256 <? (36 + offset)) = 0 :=
    (popBurn_pref endPop hpEndGuard).1.symm
  have hpEnd : offset :: tail <<+ afterEnd.stack :=
    (popBurn_pref endPop hpEndGuard).2
  have hOffsetNat : offset.toNat = dynamicOffset sevm.data head := by
    exact depositOffsetWord_toNat hOffset256
  have hEndNat : (36 + offset).toNat = 36 + dynamicOffset sevm.data head := by
    rw [B256.toNat_add_eq_of_nof]
    · rw [hOffsetNat, show (36 : B256).toNat = 36 by decide +kernel]
    · unfold B256.Nof
      rw [hOffsetNat, show (36 : B256).toNat = 36 by decide +kernel]
      omega
  have hLengthWord : 36 + dynamicOffset sevm.data head ≤ sevm.data.length := by
    have hnotLt : ¬ sevm.data.length.toB256 < 36 + offset := by
      intro hlt
      have : (sevm.data.length.toB256 <? (36 + offset)) = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos hlt]
      rw [this] at hEndFlag
      exact (by decide +kernel : (1 : B256) ≠ 0) hEndFlag
    have hwordLe : (36 + offset).toNat ≤ sevm.data.length.toB256.toNat := by
      rw [← B256.le_iff_toNat_le_toNat]
      exact le_of_not_gt hnotLt
    rw [hEndNat, B256.toNat_toB256] at hwordLe
    exact hwordLe.trans (Nat.mod_le _ _)

  rcases of_run_prepend [dup 0, pushB256 4, add, calldataload] _ run with
    ⟨afterLoad, loadRun, run⟩
  have hpLoad : Sevm.dataWord sevm (4 + offset) :: offset :: tail <<+
      afterLoad.stack := loadLength_prefix hpEnd loadRun
  have hOffsetPlusFour :
      4 + offset = Nat.toB256 (4 + dynamicOffset sevm.data head) := by
    rw [B256.add_comm]
    exact depositOffsetWord_add_four hOffset
  have hLengthLoad : Sevm.dataWord sevm (4 + offset) = length := by
    rw [hOffsetPlusFour]
    exact dataWord_depositLengthWord head (by omega)
  rw [hLengthLoad] at hpLoad

  rcases of_run_prepend
      [dup 0, pushB256 (Nat.toB256 (2 ^ 32)), swap 0, lt, iszero] _ run with
    ⟨afterLengthGuard, lengthGuardRun, run⟩
  have hpLengthGuard :
      ((length <? Nat.toB256 (2 ^ 32)) =? 0) :: length :: offset :: tail <<+
        afterLengthGuard.stack := limitGuard_prefix hpLoad lengthGuardRun
  rcases of_run_branch_call_revert hrev run with
    ⟨afterLength, lengthPop, run⟩
  have hLengthFlag :
      ((length <? Nat.toB256 (2 ^ 32)) =? 0) = 0 :=
    (popBurn_pref lengthPop hpLengthGuard).1.symm
  have hpLength : length :: offset :: tail <<+ afterLength.stack :=
    (popBurn_pref lengthPop hpLengthGuard).2
  have hLengthWordLt : length < Nat.toB256 (2 ^ 32) := by
    by_contra hnot
    have hlt : (length <? Nat.toB256 (2 ^ 32)) = 0 := by
      simp only [B256.ltCheck]
      rw [if_neg hnot]
    rw [hlt] at hLengthFlag
    exact (by decide +kernel : ((0 : B256) =? 0) ≠ 0) hLengthFlag
  have hLength256 : dynamicLength sevm.data head < 2 ^ 256 :=
    B256.toNat_lt _
  have hLength : dynamicLength sevm.data head < 2 ^ 32 := by
    have hnat := B256.toNat_lt_toNat hLengthWordLt
    rw [depositLengthWord_toNat hLength256,
      B256.toNat_toB256_of_lt (by omega)] at hnat
    exact hnat

  rcases of_run_prepend
      [dup 0, pushB256 31, add, pushB256 31, Ninst.not, Ninst.and,
        dup 2, add, pushB256 36, add, calldatasize, lt] _ run with
    ⟨afterPaddedGuard, paddedGuardRun, run⟩
  have hpPaddedGuard :
      (sevm.data.length.toB256 <? paddedEnd) :: length :: offset :: tail <<+
        afterPaddedGuard.stack := by
    simpa only [paddedEnd, rounded] using
      paddedEndGuard_prefix hpLength paddedGuardRun
  rcases of_run_branch_call_revert hrev run with
    ⟨afterPadded, paddedPop, run⟩
  have hPaddedFlag : (sevm.data.length.toB256 <? paddedEnd) = 0 :=
    (popBurn_pref paddedPop hpPaddedGuard).1.symm
  have hpPadded : length :: offset :: tail <<+ afterPadded.stack :=
    (popBurn_pref paddedPop hpPaddedGuard).2
  have hLengthNat : length.toNat = dynamicLength sevm.data head :=
    depositLengthWord_toNat hLength256
  have hCeilUpper : ceil32 (dynamicLength sevm.data head) ≤
      31 + dynamicLength sevm.data head := by
    rw [ceil32_eq_mul, Nat.mul_comm]
    exact Nat.div_mul_le_self _ _
  have hRoundedNat : rounded.toNat = ceil32 (dynamicLength sevm.data head) := by
    dsimp only [rounded, length]
    simpa only [depositLengthWord] using
      (B256.toNat_ceil32 (len := dynamicLength sevm.data head) (by omega))
  have hOffsetRoundedNat : (offset + rounded).toNat =
      dynamicOffset sevm.data head + ceil32 (dynamicLength sevm.data head) := by
    rw [B256.toNat_add_eq_of_nof]
    · rw [hOffsetNat, hRoundedNat]
    · unfold B256.Nof
      rw [hOffsetNat, hRoundedNat]
      omega
  have hPaddedEndNat : paddedEnd.toNat =
      36 + dynamicOffset sevm.data head +
        ceil32 (dynamicLength sevm.data head) := by
    dsimp only [paddedEnd]
    rw [B256.toNat_add_eq_of_nof]
    · rw [hOffsetRoundedNat,
        show (36 : B256).toNat = 36 by decide +kernel]
      omega
    · unfold B256.Nof
      rw [hOffsetRoundedNat,
        show (36 : B256).toNat = 36 by decide +kernel]
      omega
  have hPadded : 36 + dynamicOffset sevm.data head +
      ceil32 (dynamicLength sevm.data head) ≤ sevm.data.length := by
    have hnotLt : ¬ sevm.data.length.toB256 < paddedEnd := by
      intro hlt
      have : sevm.data.length.toB256 <? paddedEnd = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos hlt]
      rw [this] at hPaddedFlag
      exact (by decide +kernel : (1 : B256) ≠ 0) hPaddedFlag
    have hwordLe : paddedEnd.toNat ≤ sevm.data.length.toB256.toNat := by
      rw [← B256.le_iff_toNat_le_toNat]
      exact le_of_not_gt hnotLt
    rw [hPaddedEndNat, B256.toNat_toB256] at hwordLe
    exact hwordLe.trans (Nat.mod_le _ _)

  rcases accept_of_run hpPadded run with
    ⟨next, hpNext, bodyRun, hmemory, hstor, hcode⟩
  have hentryMemory : afterPadded.memory = pre.memory := by
    rw [← paddedPop.memory,
      ← Line.of_inv Devm.memory (by line_inv) paddedGuardRun,
      ← lengthPop.memory,
      ← Line.of_inv Devm.memory (by line_inv) lengthGuardRun,
      ← Line.of_inv Devm.memory (by line_inv) loadRun,
      ← endPop.memory,
      ← Line.of_inv Devm.memory (by line_inv) endGuardRun,
      ← offsetPop.memory,
      ← Line.of_inv Devm.memory (by line_inv) offsetGuardRun]
  have popState : ∀ {a b : Devm}, Devm.PopBurn [0] a b →
      a.state = b.state := by
    intro a b h
    exact h.state
  have storOfState : ∀ {a b : Devm}, a.state = b.state →
      Devm.getStor a = Devm.getStor b := by
    intro a b h
    funext address
    exact getStor_eq_of_state_eq h address
  have codeOfState : ∀ {a b : Devm}, a.state = b.state →
      Devm.getCode a = Devm.getCode b := by
    intro a b h
    funext address
    exact getCode_eq_of_state_eq h address
  have hentryStor : Devm.getStor pre = Devm.getStor afterPadded := by
    calc
      _ = Devm.getStor afterOffsetGuard :=
        Line.of_inv Devm.getStor (by line_inv) offsetGuardRun
      _ = Devm.getStor afterOffset :=
        storOfState (popState offsetPop)
      _ = Devm.getStor afterEndGuard :=
        Line.of_inv Devm.getStor (by line_inv) endGuardRun
      _ = Devm.getStor afterEnd :=
        storOfState (popState endPop)
      _ = Devm.getStor afterLoad :=
        Line.of_inv Devm.getStor (by line_inv) loadRun
      _ = Devm.getStor afterLengthGuard :=
        Line.of_inv Devm.getStor (by line_inv) lengthGuardRun
      _ = Devm.getStor afterLength :=
        storOfState (popState lengthPop)
      _ = Devm.getStor afterPaddedGuard :=
        Line.of_inv Devm.getStor (by line_inv) paddedGuardRun
      _ = Devm.getStor afterPadded :=
        storOfState (popState paddedPop)
  have hentryCode : Devm.getCode pre = Devm.getCode afterPadded := by
    calc
      _ = Devm.getCode afterOffsetGuard :=
        Line.of_inv Devm.getCode (by line_inv) offsetGuardRun
      _ = Devm.getCode afterOffset :=
        codeOfState (popState offsetPop)
      _ = Devm.getCode afterEndGuard :=
        Line.of_inv Devm.getCode (by line_inv) endGuardRun
      _ = Devm.getCode afterEnd :=
        codeOfState (popState endPop)
      _ = Devm.getCode afterLoad :=
        Line.of_inv Devm.getCode (by line_inv) loadRun
      _ = Devm.getCode afterLengthGuard :=
        Line.of_inv Devm.getCode (by line_inv) lengthGuardRun
      _ = Devm.getCode afterLength :=
        codeOfState (popState lengthPop)
      _ = Devm.getCode afterPaddedGuard :=
        Line.of_inv Devm.getCode (by line_inv) paddedGuardRun
      _ = Devm.getCode afterPadded :=
        codeOfState (popState paddedPop)
  refine ⟨next, ⟨hOffset, hLengthWord, hLength, hPadded⟩,
    hpNext, bodyRun, ?_, ?_, ?_⟩
  · rw [hmemory, hentryMemory]
  · rw [hstor]
    exact hentryStor.symm
  · rw [hcode]
    exact hentryCode.symm

/-- Add the actual two-instruction argument load to the successful tail
validator inversion.  The address equality is kept explicit here so concrete
ABI heads can discharge it by kernel computation. -/
private theorem validateDynamicTail_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {head : B256} {headNat : Nat} {offsetWord lengthWord : B256}
    {tail : Stack} {body : Func}
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (haddress : (32 * head) + 4 = Nat.toB256 (4 + 32 * headNat))
    (hheadBound : 4 + 32 * headNat < 2 ^ 256)
    (hp : tail <<+ pre.stack)
    (run : Func.Run fs sevm pre
      (validateDynamicTail head offsetWord lengthWord body) post) :
    ∃ next,
      DynamicTailDecodable sevm.data headNat ∧
      tail <<+ next.stack ∧
      Func.Run fs sevm next body post ∧
      next.memory =
        (pre.memory.write (lengthWord * 32).toNat
          (depositLengthWord sevm.data headNat).toBytes).write
          (offsetWord * 32).toNat
          (depositOffsetWord sevm.data headNat).toBytes ∧
      Devm.getStor next = Devm.getStor pre ∧
      Devm.getCode next = Devm.getCode pre := by
  rw [validateDynamicTail_eq] at run
  rcases of_run_prepend (arg head) _ run with
    ⟨afterArg, argRun, run⟩
  have hpArg : Sevm.argWord sevm head :: tail <<+ afterArg.stack :=
    prefix_of_arg hp argRun
  have hload : Sevm.argWord sevm head =
      depositOffsetWord sevm.data headNat := by
    unfold Sevm.argWord
    rw [haddress]
    exact dataWord_depositOffsetWord headNat hheadBound
  rw [hload] at hpArg
  rcases validateDynamicTailAfterArg_success_of_run hrev hpArg run with
    ⟨next, hdec, hpNext, bodyRun, hmemory, hstor, hcode⟩
  have hargMemory : pre.memory = afterArg.memory :=
    Line.of_inv Devm.memory (by unfold arg cdl; line_inv) argRun
  have hargStor : Devm.getStor pre = Devm.getStor afterArg :=
    Line.of_inv Devm.getStor (by unfold arg cdl; line_inv) argRun
  have hargCode : Devm.getCode pre = Devm.getCode afterArg :=
    Line.of_inv Devm.getCode (by unfold arg cdl; line_inv) argRun
  refine ⟨next, hdec, hpNext, bodyRun, ?_, ?_, ?_⟩
  · rw [hmemory, ← hargMemory]
  · exact hstor.trans hargStor.symm
  · exact hcode.trans hargCode.symm

private theorem depositHeadGuard_prefix
    {sevm : Sevm} {pre post : Devm} {tail : Stack}
    (hp : tail <<+ pre.stack)
    (run : Line.Run sevm pre [pushB256 132, calldatasize, lt] post) :
    (sevm.data.length.toB256 <? (132 : B256)) :: tail <<+
      post.stack := by
  rcases Line.of_run_cons run with ⟨s1, q1, run⟩
  have hp1 : (132 : B256) :: tail <<+ s1.stack :=
    prefix_of_push (of_run_pushB256 q1) hp
  rcases Line.of_run_cons run with ⟨s2, q2, run⟩
  have hp2 : sevm.data.length.toB256 :: (132 : B256) :: tail <<+
      s2.stack := prefix_of_push (of_run_calldatasize q2) hp1
  rcases Line.of_run_cons run with ⟨_, q3, hnil⟩
  cases hnil
  exact prefix_of_lt q3 hp2

/-- Successful execution of the complete source ABI validator yields the
independent decoder predicate and the exact six-word scratch-memory image
before entering the deposit body. -/
theorem validateDepositAbi_success_of_run
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {tail : Stack} {body : Func}
    (hrev : fs[emptyRevertSlot]? = some Func.revert)
    (hp : tail <<+ pre.stack)
    (hmemory : pre.memory = Mem.empty)
    (run : Func.Run fs sevm pre (validateDepositAbi body) post) :
    ∃ next,
      DepositAbiDecodable sevm.data
        (dynamicPayload sevm.data 0)
        (dynamicPayload sevm.data 1)
        (dynamicPayload sevm.data 2)
        (calldataWord sevm.data 100) ∧
      tail <<+ next.stack ∧
      Func.Run fs sevm next body post ∧
      next.memory = depositDecodedMemory sevm.data ∧
      Devm.getStor next = Devm.getStor pre ∧
      Devm.getCode next = Devm.getCode pre := by
  unfold validateDepositAbi at run
  rcases of_run_prepend [pushB256 132, calldatasize, lt] _ run with
    ⟨afterHeadGuard, headGuardRun, run⟩
  have hpHeadGuard :
      (sevm.data.length.toB256 <? (132 : B256)) :: tail <<+
        afterHeadGuard.stack := depositHeadGuard_prefix hp headGuardRun
  rcases of_run_branch_call_revert hrev run with
    ⟨afterHead, headPop, run⟩
  have hHeadFlag : (sevm.data.length.toB256 <? (132 : B256)) = 0 :=
    (popBurn_pref headPop hpHeadGuard).1.symm
  have hpHead : tail <<+ afterHead.stack :=
    (popBurn_pref headPop hpHeadGuard).2
  have hHead : 132 ≤ sevm.data.length := by
    have hnotLt : ¬ sevm.data.length.toB256 < (132 : B256) := by
      intro hlt
      have hcheck : (sevm.data.length.toB256 <? (132 : B256)) = 1 := by
        simp only [B256.ltCheck]
        rw [if_pos hlt]
      rw [hcheck] at hHeadFlag
      exact (by decide +kernel : (1 : B256) ≠ 0) hHeadFlag
    have hwordLe : (132 : B256).toNat ≤
        sevm.data.length.toB256.toNat := by
      rw [← B256.le_iff_toNat_le_toNat]
      exact le_of_not_gt hnotLt
    rw [show (132 : B256).toNat = 132 by decide +kernel,
      B256.toNat_toB256] at hwordLe
    exact hwordLe.trans (Nat.mod_le _ _)
  have hheadMemory : pre.memory = afterHead.memory :=
    (Line.of_inv Devm.memory (by line_inv) headGuardRun).trans
      headPop.memory
  have hheadPopState : afterHeadGuard.state = afterHead.state :=
    headPop.state
  have hheadPopStor : Devm.getStor afterHeadGuard =
      Devm.getStor afterHead := by
    funext address
    exact getStor_eq_of_state_eq hheadPopState address
  have hheadPopCode : Devm.getCode afterHeadGuard =
      Devm.getCode afterHead := by
    funext address
    exact getCode_eq_of_state_eq hheadPopState address
  have hheadStor : Devm.getStor pre = Devm.getStor afterHead :=
    (Line.of_inv Devm.getStor (by line_inv) headGuardRun).trans hheadPopStor
  have hheadCode : Devm.getCode pre = Devm.getCode afterHead :=
    (Line.of_inv Devm.getCode (by line_inv) headGuardRun).trans hheadPopCode

  rcases validateDynamicTail_success_of_run
      (head := (0 : B256)) (headNat := 0)
      (offsetWord := (0 : B256)) (lengthWord := (3 : B256))
      hrev (by decide +kernel) (by decide +kernel) hpHead run with
    ⟨afterTail0, htail0, hpTail0, run, hmemory0, hstor0, hcode0⟩
  rcases validateDynamicTail_success_of_run
      (head := (1 : B256)) (headNat := 1)
      (offsetWord := (1 : B256)) (lengthWord := (4 : B256))
      hrev (by decide +kernel) (by decide +kernel) hpTail0 run with
    ⟨afterTail1, htail1, hpTail1, run, hmemory1, hstor1, hcode1⟩
  rcases validateDynamicTail_success_of_run
      (head := (2 : B256)) (headNat := 2)
      (offsetWord := (2 : B256)) (lengthWord := (5 : B256))
      hrev (by decide +kernel) (by decide +kernel) hpTail1 run with
    ⟨next, htail2, hpNext, bodyRun, hmemory2, hstor2, hcode2⟩
  refine ⟨next, ?_, hpNext, bodyRun, ?_, ?_, ?_⟩
  · exact ⟨hHead, htail0, htail1, htail2, rfl, rfl, rfl, rfl⟩
  · unfold depositDecodedMemory
    rw [hmemory2, hmemory1, hmemory0, ← hheadMemory, hmemory]
    rw [show ((3 : B256) * 32).toNat = 96 by decide +kernel,
      show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      show ((4 : B256) * 32).toNat = 128 by decide +kernel,
      show ((1 : B256) * 32).toNat = 32 by decide +kernel,
      show ((5 : B256) * 32).toNat = 160 by decide +kernel,
      show ((2 : B256) * 32).toNat = 64 by decide +kernel]
  · exact hstor2.trans (hstor1.trans (hstor0.trans hheadStor.symm))
  · exact hcode2.trans (hcode1.trans (hcode0.trans hheadCode.symm))

end Blanc.BeaconDeposit
