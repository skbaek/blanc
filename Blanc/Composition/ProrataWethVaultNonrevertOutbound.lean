-- ProrataWethVaultNonrevertOutbound.lean : `withdraw` and `redeem` up to
-- their capacity views revert only through a refused WETH child.

import Blanc.Composition.ProrataWethVaultNonrevertInbound

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

/-!
# Walk-level revert cause of the outbound flows

As for the inbound flows, each core takes a reverting gas-exact walk of the
deployed vault and shows that it visits a refused WETH child.  After the
shared entry and the exact quote, the caller, receiver and owner guards pass
on their premises; the owner holds the burned shares because the amount is
within the capacity view; a delegated burn finds a collision-free allowance
key covering the shares; the burn cannot underflow the supply because the
ledger is conserved; and the WETH `transfer` either was refused (the
conclusion) or returned canonical `true`, after which nothing reverts.
-/

section

variable {P : Sevm → Devm → Ninst → Devm → Prop}
  {fs : List Func} {sevm : Sevm}

/-- The allowance-collision check leaves a zero flag on a key that is neither
address-shaped nor the supply word. -/
theorem checkAllowanceSlotCollision_zero {pre post : Devm} {key : B256}
    {tail : Stack}
    (hp : key :: tail <<+ pre.stack)
    (run : Line.Run sevm pre
      Blanc.ProrataWethVault.checkAllowanceSlotCollision post)
    (notAddress : ¬ ValidAdr key)
    (notSupply : key ≠ Blanc.ProrataWethVault.supplySlot) :
    (0 : B256) :: key :: tail <<+ post.stack := by
  simp only [Blanc.ProrataWethVault.checkAllowanceSlotCollision] at run
  rcases of_run_append _ run with ⟨beforeOr, guardRun, orRun⟩
  rcases of_run_append _ guardRun with ⟨beforeMax, addressRun, maxRun⟩
  rcases Line.of_run_cons addressRun with ⟨afterDup, dupRun, checkRun⟩
  have duplicated : key :: key :: tail <<+ afterDup.stack :=
    prefix_of_dup_val dupRun (by show_nth) hp
  rcases of_check_address duplicated checkRun with
    ⟨addressFlag, addressPrefix, addressZero⟩
  rcases Line.of_run_cons maxRun with ⟨afterMaxDup, maxDupRun, isMaxRun⟩
  have maxInput : key :: addressFlag :: key :: tail <<+ afterMaxDup.stack :=
    prefix_of_dup_val maxDupRun (by show_nth) addressPrefix
  simp only [isMax] at isMaxRun
  rcases Line.of_run_cons isMaxRun with ⟨afterNot, notRun, isZeroRun⟩
  rcases Line.of_run_cons isZeroRun with ⟨afterMax, zeroRun, hnil⟩
  cases hnil
  have maxPrefix : ((~~~ key) =? 0) :: addressFlag :: key :: tail <<+
      beforeOr.stack := prefix_of_iszero zeroRun (prefix_of_not notRun maxInput)
  have orPrefix := prefix_of_or (of_run_singleton orRun) maxPrefix
  have notNonzero : (~~~ key) ≠ 0 := by
    intro notZero
    exact notSupply (B256.eq_max_of_not_eq_zero notZero)
  have flagZero : ((~~~ key) =? 0) ||| addressFlag = 0 := by
    rw [addressZero.mpr notAddress]
    simp [B256.eqCheck, notNonzero]
    rfl
  rw [flagZero] at orPrefix
  exact orPrefix

/-- The guarded allowance key along an avoiding walk, on a collision-free
key: the hashed key reaches the body, and every operation word at or above
byte 64 survives. -/
theorem allowanceKey_avoiding {pre : Devm} {out : Execution} {owner : B256}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (ownerWindow : MemWordAt pre
      (Blanc.ProrataWethVault.ownerWord * 32).toNat owner)
    (notAddress :
      ¬ ValidAdr (Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256))
    (notSupply : Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256 ≠
      Blanc.ProrataWethVault.supplySlot)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.guardedAllowanceKey
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.ownerWord)
        [caller] body) out) :
    ∃ bodyPre,
      Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256 :: tail <<+
        bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      (∀ {offset : Nat} {w : B256}, 64 ≤ offset →
        MemWordAt pre offset w → MemWordAt bodyPre offset w) ∧
      Devm.getStor pre = Devm.getStor bodyPre ∧
      Devm.getCode pre = Devm.getCode bodyPre ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  simp only [Blanc.ProrataWethVault.guardedAllowanceKey] at run
  obtain ⟨s1, ownerRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p1, wf1, reads1, state1⟩ :=
    of_run_loadWordAt_image stack memoryWf (selfReads pre)
      (MemWordAt.self_toB256 ownerWindow) ownerRun
  obtain ⟨s2, ownerStoreRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p2, wf2, reads2, state2⟩ :=
    of_run_mstoreAt_image p1 wf1 reads1 ownerStoreRun
  obtain ⟨s3, callerRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p3, wf3, reads3, quiet3⟩ :=
    (Blanc.ProrataWethVault.ProducesWord.caller (sevm := sevm)
      (image := Bytes.writeAt pre.memory.data.toList
        ((0 : B256) * 32).toNat owner.toBytes)) wf2 reads2 p2 callerRun
  obtain ⟨s4, callerStoreRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p4, wf4, reads4, state4⟩ :=
    of_run_mstoreAt_image p3 wf3 reads3 callerStoreRun
  have windowImage : Mem.Reads s4.memory
      (Blanc.ProrataWethVault.allowanceKeyImage pre.memory.data.toList owner
        sevm.caller.toB256) := by
    simpa only [Blanc.ProrataWethVault.allowanceKeyImage,
      show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      show ((1 : B256) * 32).toNat = 32 by decide +kernel] using reads4
  obtain ⟨s5, pushRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have pushLine := pushRun
  simp only [pushList, List.map] at pushRun
  rcases Line.of_run_cons pushRun with ⟨_, push64Run, pushRun⟩
  rcases Line.of_run_cons pushRun with ⟨_, push0Run, pushNil⟩
  cases pushNil
  have push64 := of_run_pushB256 push64Run
  have push0 := of_run_pushB256 push0Run
  have windowPrefix : (0 : B256) :: 64 :: tail <<+ s5.stack :=
    prefix_of_push push0 (prefix_of_push push64 p4)
  have memory5 : s4.memory = s5.memory := push64.memory.trans push0.memory
  obtain ⟨s6, keccakRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have keccakSource := Ninst.Run.of_runCompiled keccakRun
  obtain ⟨hashPrefix, keccakMemory⟩ :=
    prefix_of_keccak256_val keccakSource windowPrefix
  have windowRead :
      (s5.memory.read (0 : B256).toNat (64 : B256).toNat).1 =
        owner.toBytes ++ sevm.caller.toB256.toBytes := by
    rw [show ((0 : B256)).toNat = 0 by decide +kernel,
      show ((64 : B256)).toNat = 64 by decide +kernel,
      Mem.Reads.read (memory5 ▸ windowImage)]
    simpa only [Blanc.ProrataWethVault.allowanceKeyImage] using
      Bytes.read_two_word_writes_at pre.memory.data.toList 0 owner
        sevm.caller.toB256
  have keyPrefix : Blanc.ProrataWethVault.allowanceKey owner
      sevm.caller.toB256 :: tail <<+ s6.stack := by
    rw [windowRead] at hashPrefix
    simpa only [Blanc.ProrataWethVault.allowanceKey] using hashPrefix
  obtain ⟨s7, guardRun, branchRun⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have zeroPrefix :=
    checkAllowanceSlotCollision_zero keyPrefix guardRun notAddress notSupply
  obtain ⟨bodyPre, pop, bodyRun, bodyTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  have pop' := Devm.PopBurn.of_popBurnBy pop
  have guardMemory : s6.memory = s7.memory :=
    Line.of_inv Devm.memory (by
      unfold Blanc.ProrataWethVault.checkAllowanceSlotCollision checkAddress
        isMax
      line_inv) guardRun
  have guardState : s6.state = s7.state :=
    Line.of_inv Devm.state (by
      unfold Blanc.ProrataWethVault.checkAllowanceSlotCollision checkAddress
        isMax
      line_inv) guardRun
  have memoryEnd : bodyPre.memory = s5.memory.extend (0 : B256).toNat
      (64 : B256).toNat := by
    rw [← pop'.memory, ← guardMemory, keccakMemory]
  refine ⟨bodyPre, bodyTail, ?_, ?_, ?_, ?_, bodyRun⟩
  · rw [memoryEnd, ← memory5]
    exact wf4.extend _ _
  · intro offset w above window
    have w2 : MemWordAt s2 offset w :=
      (window.acrossLoadWord ownerRun).acrossMstoreAt
        (Or.inr (by
          rw [show ((0 : B256) * 32).toNat = 0 by decide +kernel]
          omega)) ownerStoreRun
    have w3 : MemWordAt s3 offset w :=
      w2.acrossLine (by line_inv) callerRun
    have w4 : MemWordAt s4 offset w :=
      w3.acrossMstoreAt
        (Or.inr (by
          rw [show ((1 : B256) * 32).toNat = 32 by decide +kernel]
          omega)) callerStoreRun
    exact MemWordAt.extend (memoryEnd.trans (by rw [← memory5]))
      w4
  · have state14 : pre.state = s4.state :=
      state1.trans (state2.trans (quiet3.1.trans state4))
    have state45 : s4.state = s5.state :=
      Line.of_inv Devm.state (by line_inv) pushLine
    exact (funext (getStor_eq_of_state_eq (state14.trans state45))).trans
      ((Ninst.Hinv.inv (f := Devm.getStor) keccakSource).trans
        (funext (getStor_eq_of_state_eq (guardState.trans pop'.state))))
  · have state14 : pre.state = s4.state :=
      state1.trans (state2.trans (quiet3.1.trans state4))
    have state45 : s4.state = s5.state :=
      Line.of_inv Devm.state (by line_inv) pushLine
    exact (funext (getCode_eq_of_state_eq (state14.trans state45))).trans
      ((Blanc.ProrataWethVault.register_getCode keccakSource).symm.trans
        (funext (getCode_eq_of_state_eq (guardState.trans pop'.state))))


/-- The owner-holds-shares guard passes when the booked owner balance covers
the burned shares; the balance is staged at its operation word. -/
theorem ownerHasShares_avoiding {pre : Devm} {out : Execution}
    {sharesWord owner shares : B256} {body : Func} {tail : Stack}
    (ownerWindow : MemWordAt pre
      (Blanc.ProrataWethVault.ownerWord * 32).toNat owner)
    (sharesWindow : MemWordAt pre (sharesWord * 32).toNat shares)
    (sharesMiss : (sharesWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (covered :
      shares.toNat ≤ (Devm.getStorVal pre sevm.currentTarget owner).toNat)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.ownerHasShares
        (Blanc.ProrataWethVault.loadWord sharesWord) body) out) :
    ∃ bodyPre, tail <<+ bodyPre.stack ∧ Mem.Wf bodyPre.memory ∧
      MemWordAt bodyPre (Blanc.ProrataWethVault.balanceWord * 32).toNat
        (Devm.getStorVal pre sevm.currentTarget owner) ∧
      (∀ {offset : Nat} {w : B256},
        (offset + 32 ≤ (Blanc.ProrataWethVault.balanceWord * 32).toNat ∨
          (Blanc.ProrataWethVault.balanceWord * 32).toNat + 32 ≤ offset) →
        MemWordAt pre offset w → MemWordAt bodyPre offset w) ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  unfold Blanc.ProrataWethVault.ownerHasShares at run
  obtain ⟨s1, ownerRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p1 := prefix_of_loadWord_window ownerWindow stack ownerRun
  have state1 : pre.state = s1.state :=
    Line.of_inv Devm.state
      (by unfold Blanc.ProrataWethVault.loadWord; line_inv) ownerRun
  obtain ⟨s2, sloadRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨balance, p2, balanceEq⟩ := prefix_of_sload sloadSource p1
  have balanceValue : balance =
      Devm.getStorVal pre sevm.currentTarget owner := by
    rw [balanceEq]
    change (Devm.getStor s1 sevm.currentTarget).get owner =
      (Devm.getStor pre sevm.currentTarget).get owner
    rw [funext (getStor_eq_of_state_eq state1)]
  subst balanceValue
  have state2 : s1.state = s2.state :=
    Ninst.Hinv.inv (f := Devm.state) sloadSource
  have wf2 : Mem.Wf s2.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) sloadSource]
    exact (ownerWindow.acrossLoadWord ownerRun).1
  obtain ⟨s3, balanceStoreRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p3, wf3, balanceWindow, balanceMiss, state3⟩ :=
    mstoreAt_window p2 wf2 balanceStoreRun
  have move3 : ∀ {offset : Nat} {w : B256},
      (offset + 32 ≤ (Blanc.ProrataWethVault.balanceWord * 32).toNat ∨
        (Blanc.ProrataWethVault.balanceWord * 32).toNat + 32 ≤ offset) →
      MemWordAt pre offset w → MemWordAt s3 offset w := fun miss window =>
    balanceMiss miss ((window.acrossLoadWord ownerRun).acrossNinst sloadSource)
  obtain ⟨s4, sharesRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p4 := prefix_of_loadWord_window (move3 (Or.inl sharesMiss) sharesWindow)
    p3 sharesRun
  obtain ⟨s5, balanceRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p5 := prefix_of_loadWord_window (balanceWindow.acrossLoadWord sharesRun)
    p4 balanceRun
  obtain ⟨s6, ltRun, -, branchRun⟩ := Func.RunCompiledToAvoiding.next_inv run
  have ltSource := Ninst.Run.of_runCompiled ltRun
  have flag := prefix_of_lt ltSource p5
  have notLess : ¬ Devm.getStorVal pre sevm.currentTarget owner < shares := by
    intro less
    have := B256.toNat_lt_toNat less
    omega
  have zeroPrefix : (0 : B256) :: tail <<+ s6.stack := by
    simpa [B256.ltCheck, notLess] using flag
  obtain ⟨bodyPre, pop, bodyRun, bodyTail⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  have pop' := Devm.PopBurn.of_popBurnBy pop
  have memoryTail : s5.memory = bodyPre.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) ltSource).trans pop'.memory
  have moveTail : ∀ {offset : Nat} {w : B256}, MemWordAt s3 offset w →
      MemWordAt bodyPre offset w := fun window =>
    MemWordAt.of_memory_eq memoryTail.symm
      ((window.acrossLoadWord sharesRun).acrossLoadWord balanceRun)
  refine ⟨bodyPre, bodyTail, (moveTail balanceWindow).1, moveTail balanceWindow,
    fun miss window => moveTail (move3 miss window), ?_, bodyRun⟩
  exact state1.trans (state2.trans (state3.trans
    ((Line.of_inv Devm.state (by
        unfold Blanc.ProrataWethVault.loadWord; line_inv) sharesRun).trans
      ((Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) balanceRun).trans
        ((Ninst.Hinv.inv (f := Devm.state) ltSource).trans pop'.state)))))


/-- A delegated burn's allowance spend along an avoiding walk: on a
collision-free key whose allowance covers the shares, the walk reaches the
burn continuation.  Every operation word at or above byte 64 other than the
scratch and allowance words survives, and so does the WETH configuration. -/
theorem spendAllowance_avoiding {pre : Devm} {out : Execution}
    {sharesWord owner shares : B256} {k : Nat} {body : Func} {tail : Stack}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (ownerWindow : MemWordAt pre
      (Blanc.ProrataWethVault.ownerWord * 32).toNat owner)
    (sharesWindow : MemWordAt pre (sharesWord * 32).toNat shares)
    (sharesAbove : 64 ≤ (sharesWord * 32).toNat)
    (sharesMissScratch :
      (Blanc.ProrataWethVault.scratchWord * 32).toNat + 32 ≤
        (sharesWord * 32).toNat)
    (sharesMissAllowance : (sharesWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.allowanceWord * 32).toNat)
    (notAddress :
      ¬ ValidAdr (Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256))
    (notSupply : Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256 ≠
      Blanc.ProrataWethVault.supplySlot)
    (covered : shares.toNat ≤ (Devm.getStorVal pre sevm.currentTarget
      (Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256)).toNat)
    (lookup : fs[k]? = some body)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.spendAllowance
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.ownerWord)
        [caller] (Blanc.ProrataWethVault.loadWord sharesWord) k) out) :
    ∃ bodyPre, Mem.Wf bodyPre.memory ∧
      (∀ {offset : Nat} {w : B256}, 64 ≤ offset →
        (offset + 32 ≤ (Blanc.ProrataWethVault.scratchWord * 32).toNat ∨
          (Blanc.ProrataWethVault.scratchWord * 32).toNat + 32 ≤ offset) →
        (offset + 32 ≤ (Blanc.ProrataWethVault.allowanceWord * 32).toNat ∨
          (Blanc.ProrataWethVault.allowanceWord * 32).toNat + 32 ≤ offset) →
        MemWordAt pre offset w → MemWordAt bodyPre offset w) ∧
      DirectWethConfiguration sevm.currentTarget sevm bodyPre ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  unfold Blanc.ProrataWethVault.spendAllowance at run
  obtain ⟨s1, keyStack, wf1, carry1, storage1, code1, run⟩ :=
    allowanceKey_avoiding memoryWf ownerWindow notAddress notSupply stack run
  have config1 : DirectWethConfiguration sevm.currentTarget sevm s1 :=
    config.of_code_eq (congrFun code1 wethAccount).symm
  obtain ⟨s2, scratchStore, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p2, wf2, scratchWindow, scratchMiss, state2⟩ :=
    mstoreAt_window keyStack wf1 scratchStore
  obtain ⟨s3, scratchLoad, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p3 := prefix_of_loadWord_window scratchWindow p2 scratchLoad
  have state3 : s2.state = s3.state :=
    Line.of_inv Devm.state
      (by unfold Blanc.ProrataWethVault.loadWord; line_inv) scratchLoad
  obtain ⟨s4, sloadRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨allowance, p4, allowanceEq⟩ := prefix_of_sload sloadSource p3
  have allowanceValue : allowance = Devm.getStorVal pre sevm.currentTarget
      (Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256) := by
    rw [allowanceEq]
    change (Devm.getStor s3 sevm.currentTarget).get _ =
      (Devm.getStor pre sevm.currentTarget).get _
    rw [storage1, funext (getStor_eq_of_state_eq (state2.trans state3))]
  rw [← allowanceValue] at covered
  have wf4 : Mem.Wf s4.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) sloadSource]
    exact (scratchWindow.acrossLoadWord scratchLoad).1
  have state4 : s3.state = s4.state :=
    Ninst.Hinv.inv (f := Devm.state) sloadSource
  obtain ⟨s5, allowanceStore, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p5, -, allowanceWindow, allowanceMiss, state5⟩ :=
    mstoreAt_window p4 wf4 allowanceStore
  have move5 : ∀ {offset : Nat} {w : B256}, 64 ≤ offset →
      (offset + 32 ≤ (Blanc.ProrataWethVault.scratchWord * 32).toNat ∨
        (Blanc.ProrataWethVault.scratchWord * 32).toNat + 32 ≤ offset) →
      (offset + 32 ≤ (Blanc.ProrataWethVault.allowanceWord * 32).toNat ∨
        (Blanc.ProrataWethVault.allowanceWord * 32).toNat + 32 ≤ offset) →
      MemWordAt pre offset w → MemWordAt s5 offset w := by
    intro offset w above scratchOff allowanceOff window
    exact allowanceMiss allowanceOff
      (((scratchMiss scratchOff (carry1 above window)).acrossLoadWord
        scratchLoad).acrossNinst sloadSource)
  have config5 : DirectWethConfiguration sevm.currentTarget sevm s5 :=
    config1.of_state_eq' (state2.trans (state3.trans (state4.trans state5)))
  obtain ⟨s6, allowanceLoad, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p6 := prefix_of_loadWord_window allowanceWindow p5 allowanceLoad
  obtain ⟨s7, maxLine, branchRun⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have maxLine' := maxLine
  simp only [isMax] at maxLine
  rcases Line.of_run_cons maxLine with ⟨_, notRun, maxLine⟩
  rcases Line.of_run_cons maxLine with ⟨_, zeroRun, hnil⟩
  cases hnil
  have maxFlag := prefix_of_iszero zeroRun (prefix_of_not notRun p6)
  have move7 : ∀ {offset : Nat} {w : B256}, MemWordAt s5 offset w →
      MemWordAt s7 offset w := fun window =>
    (window.acrossLoadWord allowanceLoad).acrossLine (by line_inv) maxLine'
  have state7 : s5.state = s7.state :=
    (Line.of_inv Devm.state
      (by unfold Blanc.ProrataWethVault.loadWord; line_inv) allowanceLoad).trans
      (Line.of_inv Devm.state (by line_inv) maxLine')
  by_cases allowanceMax : allowance = B256.max
  · have onePrefix : (1 : B256) :: tail <<+ s7.stack := by
      simpa [allowanceMax, B256.not_max, B256.eqCheck] using maxFlag
    obtain ⟨callPre, pop, callRun, -⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix (by decide) onePrefix
        branchRun
    have pop' := Devm.PopBurn.of_popBurnBy pop
    obtain ⟨bodyPre, burn, bodyRun⟩ :=
      Func.RunCompiledToAvoiding.call_inv lookup callRun
    have burn' := Devm.Burn.of_burnBy burn
    have memoryEnd : s7.memory = bodyPre.memory :=
      pop'.memory.trans burn'.memory
    refine ⟨bodyPre, ?_, ?_, ?_, bodyRun⟩
    · exact MemWordAt.of_memory_eq memoryEnd.symm (move7 allowanceWindow) |>.1
    · intro offset w above scratchOff allowanceOff window
      exact MemWordAt.of_memory_eq memoryEnd.symm
        (move7 (move5 above scratchOff allowanceOff window))
    · exact config5.of_state_eq' (state7.trans (pop'.state.trans burn'.state))
  · have notNonzero : (~~~ allowance) ≠ 0 := by
      intro notZero
      exact allowanceMax (B256.eq_max_of_not_eq_zero notZero)
    have zeroPrefix : (0 : B256) :: tail <<+ s7.stack := by
      simpa [B256.eqCheck, notNonzero] using maxFlag
    obtain ⟨checkPre, pop, run, checkTail⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
    have pop' := Devm.PopBurn.of_popBurnBy pop
    have move8 : ∀ {offset : Nat} {w : B256}, MemWordAt s5 offset w →
        MemWordAt checkPre offset w := fun window =>
      MemWordAt.of_memory_eq pop'.memory.symm (move7 window)
    have sharesAt8 := move8 (move5 sharesAbove (Or.inr sharesMissScratch)
      (Or.inl sharesMissAllowance) sharesWindow)
    have allowanceAt8 := move8 allowanceWindow
    obtain ⟨c1, sharesLoad, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    have q1 := prefix_of_loadWord_window sharesAt8 checkTail sharesLoad
    obtain ⟨c2, allowanceLoad2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    have q2 := prefix_of_loadWord_window
      (allowanceAt8.acrossLoadWord sharesLoad) q1 allowanceLoad2
    obtain ⟨c3, ltRun, -, spendBranch⟩ :=
      Func.RunCompiledToAvoiding.next_inv run
    have ltSource := Ninst.Run.of_runCompiled ltRun
    have notLess : ¬ allowance < shares := by
      intro less
      have := B256.toNat_lt_toNat less
      omega
    have spendZero : (0 : B256) :: tail <<+ c3.stack := by
      simpa [B256.ltCheck, notLess] using prefix_of_lt ltSource q2
    obtain ⟨spendPre, pop2, run, spendTail⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix spendZero spendBranch
    have pop2' := Devm.PopBurn.of_popBurnBy pop2
    obtain ⟨d1, sharesLoad2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨d2, allowanceLoad3, run⟩ :=
      Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨d3, subRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
    obtain ⟨d4, scratchLoad2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨d5, sstoreRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
    obtain ⟨bodyPre, burn, bodyRun⟩ :=
      Func.RunCompiledToAvoiding.call_inv lookup run
    have burn' := Devm.Burn.of_burnBy burn
    have subSource := Ninst.Run.of_runCompiled subRun
    have sstoreSource := Ninst.Run.of_runCompiled sstoreRun
    have moveEnd : ∀ {offset : Nat} {w : B256}, MemWordAt checkPre offset w →
        MemWordAt bodyPre offset w := by
      intro offset w window
      have atD5 : MemWordAt d5 offset w :=
        ((((((((window.acrossLoadWord sharesLoad).acrossLoadWord
          allowanceLoad2).acrossNinst ltSource).of_memory_eq
            pop2'.memory.symm).acrossLoadWord sharesLoad2).acrossLoadWord
              allowanceLoad3).acrossNinst subSource).acrossLoadWord
                scratchLoad2).acrossNinst sstoreSource
      exact MemWordAt.of_memory_eq burn'.memory.symm atD5
    have state8 : s7.state = checkPre.state := pop'.state
    have stateD4 : checkPre.state = d4.state := by
      rw [← Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) scratchLoad2,
        ← Ninst.Hinv.inv (f := Devm.state) subSource,
        ← Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) allowanceLoad3,
        ← Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) sharesLoad2,
        ← pop2'.state, ← Ninst.Hinv.inv (f := Devm.state) ltSource,
        ← Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) allowanceLoad2,
        ← Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) sharesLoad]
    have configD4 : DirectWethConfiguration sevm.currentTarget sevm d4 :=
      config5.of_state_eq' (state7.trans (state8.trans stateD4))
    refine ⟨bodyPre, (moveEnd sharesAt8).1, ?_, ?_, bodyRun⟩
    · intro offset w above scratchOff allowanceOff window
      exact moveEnd (move8 (move5 above scratchOff allowanceOff window))
    · exact (configD4.of_runCompiled sstoreRun).of_state_eq' burn'.state


/-- The shared outbound burn along an avoiding walk: the supply guard passes
on shares within the staged supply, and after the burn the WETH `transfer`
either was refused or returned canonical `true`, after which nothing
reverts. -/
theorem outboundBurn_revert {pre d : Devm} {sharesWord assetsSourceWord : B256}
    {receiver shares assets supply : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (sharesWindow : MemWordAt pre (sharesWord * 32).toNat shares)
    (assetsWindow : MemWordAt pre (assetsSourceWord * 32).toNat assets)
    (supplyWindow : MemWordAt pre
      (Blanc.ProrataWethVault.supplyWord * 32).toNat supply)
    (receiverWindow : MemWordAt pre
      (Blanc.ProrataWethVault.receiverWord * 32).toNat receiver)
    (assetsAbove : 64 ≤ (assetsSourceWord * 32).toNat)
    (receiverValid : ValidAdr receiver)
    (sharesLe : shares.toNat ≤ supply.toNat)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm pre
      (Blanc.ProrataWethVault.finishOutbound
        (Blanc.ProrataWethVault.loadWord sharesWord)
        (Blanc.ProrataWethVault.loadWord assetsSourceWord)
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord))
      (.error (.revert, d))) : False := by
  rw [Blanc.ProrataWethVault.finishOutbound_shape] at run
  obtain ⟨s1, l1, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨s2, l2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨s3, subRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  obtain ⟨s4, l4, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨s5, sstoreRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have subSource := Ninst.Run.of_runCompiled subRun
  have sstoreSource := Ninst.Run.of_runCompiled sstoreRun
  have move5 : ∀ {offset : Nat} {w : B256}, MemWordAt pre offset w →
      MemWordAt s5 offset w := fun window =>
    ((((window.acrossLoadWord l1).acrossLoadWord l2).acrossNinst
      subSource).acrossLoadWord l4).acrossNinst sstoreSource
  have config4 : DirectWethConfiguration sevm.currentTarget sevm s4 :=
    config.of_state_eq' ((Line.of_inv Devm.state (by
        unfold Blanc.ProrataWethVault.loadWord; line_inv) l1).trans
      ((Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) l2).trans
        ((Ninst.Hinv.inv (f := Devm.state) subSource).trans
          (Line.of_inv Devm.state (by
            unfold Blanc.ProrataWethVault.loadWord; line_inv) l4))))
  have config5 := config4.of_runCompiled sstoreRun
  obtain ⟨s6, sharesLoad, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have q6 := prefix_of_loadWord_window (move5 sharesWindow) nil_pref sharesLoad
  obtain ⟨s7, supplyLoad, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have q7 := prefix_of_loadWord_window
    ((move5 supplyWindow).acrossLoadWord sharesLoad) q6 supplyLoad
  obtain ⟨s8, ltRun, -, branchRun⟩ := Func.RunCompiledToAvoiding.next_inv run
  have ltSource := Ninst.Run.of_runCompiled ltRun
  have notLess : ¬ supply < shares := by
    intro less
    have := B256.toNat_lt_toNat less
    omega
  have zeroPrefix : (0 : B256) :: [] <<+ s8.stack := by
    simpa [B256.ltCheck, notLess] using prefix_of_lt ltSource q7
  obtain ⟨s9, pop, run, -⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  have pop' := Devm.PopBurn.of_popBurnBy pop
  have move9 : ∀ {offset : Nat} {w : B256}, MemWordAt s5 offset w →
      MemWordAt s9 offset w := fun window =>
    MemWordAt.of_memory_eq pop'.memory.symm
      (((window.acrossLoadWord sharesLoad).acrossLoadWord supplyLoad).acrossNinst
        ltSource)
  have config9 : DirectWethConfiguration sevm.currentTarget sevm s9 :=
    config5.of_state_eq' ((Line.of_inv Devm.state (by
        unfold Blanc.ProrataWethVault.loadWord; line_inv) sharesLoad).trans
      ((Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) supplyLoad).trans
        ((Ninst.Hinv.inv (f := Devm.state) ltSource).trans pop'.state)))
  obtain ⟨t1, m1, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨t2, m2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨t3, burnSub, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  obtain ⟨t4, slotLine, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨t5, supplyStore, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  obtain ⟨t6, logLine, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have burnSubSource := Ninst.Run.of_runCompiled burnSub
  have supplyStoreSource := Ninst.Run.of_runCompiled supplyStore
  have config4' : DirectWethConfiguration sevm.currentTarget sevm t4 :=
    config9.of_state_eq' ((Line.of_inv Devm.state (by
        unfold Blanc.ProrataWethVault.loadWord; line_inv) m1).trans
      ((Line.of_inv Devm.state (by
          unfold Blanc.ProrataWethVault.loadWord; line_inv) m2).trans
        ((Ninst.Hinv.inv (f := Devm.state) burnSubSource).trans
          (Line.of_inv Devm.state (by
            unfold Blanc.ProrataWethVault.pushSupplySlot; line_inv)
            slotLine))))
  have config6 : DirectWethConfiguration sevm.currentTarget sevm t6 :=
    (config4'.of_runCompiled supplyStore).of_code_eq
      (congrFun (Line.of_inv Devm.getCode (by
        unfold Blanc.ProrataWethVault.logBurnTransfer
          Blanc.ProrataWethVault.loadWord mstoreAt logWith
        line_inv) logLine) wethAccount).symm
  have moveT : ∀ {offset : Nat} {w : B256}, 32 ≤ offset →
      MemWordAt s9 offset w → MemWordAt t6 offset w := by
    intro offset w above window
    have atT5 : MemWordAt t5 offset w :=
      ((((window.acrossLoadWord m1).acrossLoadWord m2).acrossNinst
        burnSubSource).acrossLine (by
          unfold Blanc.ProrataWethVault.pushSupplySlot; line_inv)
          slotLine).acrossNinst supplyStoreSource
    simp only [Blanc.ProrataWethVault.logBurnTransfer, List.append_assoc]
      at logLine
    obtain ⟨u1, r1, logLine⟩ := of_run_append _ logLine
    obtain ⟨u2, r2, logLine⟩ := of_run_append _ logLine
    obtain ⟨u3, r3, logLine⟩ := of_run_append _ logLine
    obtain ⟨u4, r4, logLine⟩ := of_run_append _ logLine
    obtain ⟨u5, r5, r6⟩ := of_run_append _ logLine
    exact ((((atT5.acrossLoadWord r1).acrossMstoreAt (Or.inr (by
      rw [show ((0 : B256) * 32).toNat = 0 by decide +kernel]
      omega)) r2).acrossLine (by line_inv) r3).acrossLoadWord r4
        |>.acrossLine (by line_inv) r5).acrossLogWith r6
  have receiverAt6 := moveT (by decide +kernel) (move9 (move5 receiverWindow))
  have assetsAt6 := moveT (by omega) (move9 (move5 assetsWindow))
  obtain ⟨receiverAdr, rfl⟩ := receiverValid
  obtain ⟨bodyPre, bodyRun⟩ :=
    callWethTransfer_avoiding config6 ⟨receiverAt6.1, selfReads t6⟩
      (receiverAt6.slice_eq (selfReads t6)) (assetsAt6.slice_eq (selfReads t6))
      (by decide +kernel) assetsAbove run
  have free : Func.revertFreeIn []
      (Blanc.ProrataWethVault.logWithdraw
          (Blanc.ProrataWethVault.loadWord assetsSourceWord)
          (Blanc.ProrataWethVault.loadWord sharesWord) +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord +++
        Blanc.ProrataWethVault.returnWord) = true := by
    simp [Func.revertFreeIn_prepend, Func.revertFreeIn,
      Blanc.ProrataWethVault.returnWord, returnMemoryRange, Func.return_]
  exact Func.RunCompiledTo.not_revert_of_revertFreeIn (safe := [])
    (fun _ member => absurd member List.not_mem_nil) bodyRun.1 free d rfl


/-- The shared outbound continuation after the quote is staged: with the
caller, receiver, owner, share balance and authorization passing on their
premises, the only way it reverts is through a refused `transfer`. -/
theorem outboundGuardedTail_revert {entry d : Devm}
    {sharesWord assetsSourceWord : B256} {burnSlot : Nat}
    {receiver owner supply shares assets : B256} {tail : Stack}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (receiverWindow : MemWordAt entry
      (Blanc.ProrataWethVault.receiverWord * 32).toNat receiver)
    (ownerWindow : MemWordAt entry
      (Blanc.ProrataWethVault.ownerWord * 32).toNat owner)
    (supplyWindow : MemWordAt entry
      (Blanc.ProrataWethVault.supplyWord * 32).toNat supply)
    (sharesWindow : MemWordAt entry (sharesWord * 32).toNat shares)
    (assetsWindow : MemWordAt entry (assetsSourceWord * 32).toNat assets)
    (sharesAbove : 896 ≤ (sharesWord * 32).toNat)
    (sharesBelow : (sharesWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (assetsAbove : 896 ≤ (assetsSourceWord * 32).toNat)
    (assetsBelow : (assetsSourceWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr receiver) (receiverNonzero : receiver ≠ 0)
    (ownerValid : ValidAdr owner) (ownerNonzero : owner ≠ 0)
    (sharesLeBalance :
      shares.toNat ≤ (Devm.getStorVal entry sevm.currentTarget owner).toNat)
    (authorized :
      sevm.caller.toB256 = owner ∨
        (¬ ValidAdr (Blanc.ProrataWethVault.allowanceKey owner
            sevm.caller.toB256) ∧
          Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256 ≠
            Blanc.ProrataWethVault.supplySlot ∧
          shares.toNat ≤ (Devm.getStorVal entry sevm.currentTarget
            (Blanc.ProrataWethVault.allowanceKey owner
              sevm.caller.toB256)).toNat))
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor entry sevm.currentTarget))
    (supplyEq : supply = Devm.getStorVal entry sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (burnLookup : fs[burnSlot]? = some
      (Blanc.ProrataWethVault.finishOutbound
        (Blanc.ProrataWethVault.loadWord sharesWord)
        (Blanc.ProrataWethVault.loadWord assetsSourceWord)
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord)))
    (stack : tail <<+ entry.stack)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm entry
      (Blanc.ProrataWethVault.nonzeroCaller
        (Blanc.ProrataWethVault.nonzeroStagedAddress
          Blanc.ProrataWethVault.receiverWord
          (Blanc.ProrataWethVault.nonzeroStagedAddress
            Blanc.ProrataWethVault.ownerWord
            (Blanc.ProrataWethVault.ownerHasShares
              (Blanc.ProrataWethVault.loadWord sharesWord)
              (Blanc.ProrataWethVault.loadWord
                  Blanc.ProrataWethVault.ownerWord +++ caller ::: eq :::
                (.call burnSlot <?>
                  Blanc.ProrataWethVault.spendAllowance
                    (Blanc.ProrataWethVault.loadWord
                      Blanc.ProrataWethVault.ownerWord) [caller]
                    (Blanc.ProrataWethVault.loadWord sharesWord)
                    burnSlot))))))
      (.error (.revert, d))) : False := by
  have sharesLe : shares.toNat ≤ supply.toNat := by
    obtain ⟨ownerAdr, rfl⟩ := ownerValid
    have booked := conserved.le_supply ownerAdr
    have supplyNat := congrArg B256.toNat supplyEq
    change shares.toNat ≤ (Stor.rest (Devm.getStor entry sevm.currentTarget)
      ownerAdr).toNat at sharesLeBalance
    change supply.toNat = ((Devm.getStor entry sevm.currentTarget).get
      Blanc.ProrataWethVault.supplySlot).toNat at supplyNat
    omega
  obtain ⟨s1, p1, memory1, state1, run⟩ :=
    nonzeroCaller_avoiding callerNonzero stack run
  have wf1 : Mem.Wf s1.memory := memory1 ▸ memoryWf
  have move1 : ∀ {offset : Nat} {w : B256}, MemWordAt entry offset w →
      MemWordAt s1 offset w := fun window =>
    MemWordAt.of_memory_eq memory1.symm window
  unfold Blanc.ProrataWethVault.nonzeroStagedAddress at run
  obtain ⟨s2, p2, wf2, reads2, state2, run⟩ :=
    canonicalNonzero_avoiding wf1 (selfReads s1)
      (Blanc.ProrataWethVault.ProducesWord.loadWord
        (MemWordAt.self_toB256 (move1 receiverWindow)))
      receiverValid receiverNonzero p1 run
  have move2 : ∀ {offset : Nat} {w : B256}, MemWordAt entry offset w →
      MemWordAt s2 offset w := fun window =>
    MemWordAt.of_selfReads (move1 window) wf2 reads2
  obtain ⟨s3, p3, wf3, reads3, state3, run⟩ :=
    canonicalNonzero_avoiding wf2 (selfReads s2)
      (Blanc.ProrataWethVault.ProducesWord.loadWord
        (MemWordAt.self_toB256 (move2 ownerWindow)))
      ownerValid ownerNonzero p2 run
  have move3 : ∀ {offset : Nat} {w : B256}, MemWordAt entry offset w →
      MemWordAt s3 offset w := fun window =>
    MemWordAt.of_selfReads (move2 window) wf3 reads3
  have state13 : entry.state = s3.state := state1.trans (state2.trans state3)
  have storage3 : Devm.getStor s3 = Devm.getStor entry :=
    (funext (getStor_eq_of_state_eq state13)).symm
  obtain ⟨s4, p4, wf4, -, carry4, state4, run⟩ :=
    ownerHasShares_avoiding (move3 ownerWindow) (move3 sharesWindow)
      sharesBelow
      (by
        change shares.toNat ≤
          ((Devm.getStor s3 sevm.currentTarget).get owner).toNat
        rw [storage3]
        exact sharesLeBalance) p3 run
  have move4 : ∀ {offset : Nat} {w : B256},
      (offset + 32 ≤ (Blanc.ProrataWethVault.balanceWord * 32).toNat ∨
        (Blanc.ProrataWethVault.balanceWord * 32).toNat + 32 ≤ offset) →
      MemWordAt entry offset w → MemWordAt s4 offset w := fun miss window =>
    carry4 miss (move3 window)
  have config4 : DirectWethConfiguration sevm.currentTarget sevm s4 :=
    config.of_state_eq' (state13.trans state4)
  have storage4 : Devm.getStor s4 = Devm.getStor entry :=
    (funext (getStor_eq_of_state_eq state4)).symm.trans storage3
  obtain ⟨s5, ownerLoad, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have q5 := prefix_of_loadWord_window
    (move4 (Or.inl (by decide +kernel)) ownerWindow) p4 ownerLoad
  obtain ⟨s6, callerRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have callerSource := Ninst.Run.of_runCompiled callerRun
  have callerPush := of_run_caller callerSource
  obtain ⟨s7, eqRun, -, branchRun⟩ := Func.RunCompiledToAvoiding.next_inv run
  have eqSource := Ninst.Run.of_runCompiled eqRun
  have flag := prefix_of_eq eqSource (prefix_of_push callerPush q5)
  have move7 : ∀ {offset : Nat} {w : B256}, MemWordAt s4 offset w →
      MemWordAt s7 offset w := fun window =>
    ((window.acrossLoadWord ownerLoad).of_memory_eq callerPush.memory.symm
      ).acrossNinst eqSource
  have state7 : s4.state = s7.state :=
    (Line.of_inv Devm.state
      (by unfold Blanc.ProrataWethVault.loadWord; line_inv) ownerLoad).trans
      (callerPush.state.trans (Ninst.Hinv.inv (f := Devm.state) eqSource))
  have supplyMiss : (Blanc.ProrataWethVault.supplyWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat := by decide +kernel
  have receiverMiss : (Blanc.ProrataWethVault.receiverWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat := by decide +kernel
  by_cases selfBurn : sevm.caller.toB256 = owner
  · have onePrefix : (1 : B256) :: tail <<+ s7.stack := by
      simpa [B256.eqCheck, selfBurn] using flag
    obtain ⟨callPre, pop, callRun, -⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix (by decide) onePrefix
        branchRun
    have pop' := Devm.PopBurn.of_popBurnBy pop
    obtain ⟨burnPre, burn, burnRun⟩ :=
      Func.RunCompiledToAvoiding.call_inv burnLookup callRun
    have burn' := Devm.Burn.of_burnBy burn
    have memoryEnd : s7.memory = burnPre.memory :=
      pop'.memory.trans burn'.memory
    have moveB : ∀ {offset : Nat} {w : B256}, MemWordAt s4 offset w →
        MemWordAt burnPre offset w := fun window =>
      MemWordAt.of_memory_eq memoryEnd.symm (move7 window)
    exact outboundBurn_revert
      (config4.of_state_eq' (state7.trans (pop'.state.trans burn'.state)))
      (moveB (move4 (Or.inl sharesBelow) sharesWindow))
      (moveB (move4 (Or.inl assetsBelow) assetsWindow))
      (moveB (move4 (Or.inl supplyMiss) supplyWindow))
      (moveB (move4 (Or.inl receiverMiss) receiverWindow))
      (by omega) receiverValid sharesLe burnRun
  · have zeroPrefix : (0 : B256) :: tail <<+ s7.stack := by
      simpa [B256.eqCheck, selfBurn] using flag
    obtain ⟨spendPre, pop, spendRun, spendTail⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
    have pop' := Devm.PopBurn.of_popBurnBy pop
    have moveS : ∀ {offset : Nat} {w : B256}, MemWordAt s4 offset w →
        MemWordAt spendPre offset w := fun window =>
      MemWordAt.of_memory_eq pop'.memory.symm (move7 window)
    have storageS : Devm.getStor spendPre = Devm.getStor entry :=
      (funext (getStor_eq_of_state_eq (state7.trans pop'.state))).symm.trans
        storage4
    rcases authorized with ownerCaller | ⟨notAddress, notSupply, covered⟩
    · exact selfBurn ownerCaller
    have sharesS := moveS (move4 (Or.inl sharesBelow) sharesWindow)
    obtain ⟨burnPre, -, carryB, configB, burnRun⟩ :=
      spendAllowance_avoiding
        (config4.of_state_eq' (state7.trans pop'.state)) sharesS.1
        (moveS (move4 (Or.inl (by decide +kernel)) ownerWindow)) sharesS
        (by omega) (by
          have : (Blanc.ProrataWethVault.scratchWord * 32).toNat = 800 := by
            decide +kernel
          omega)
        (by
          have : (Blanc.ProrataWethVault.allowanceWord * 32).toNat = 1248 := by
            decide +kernel
          have : (Blanc.ProrataWethVault.balanceWord * 32).toNat = 1216 := by
            decide +kernel
          omega)
        notAddress notSupply
        (by
          change shares.toNat ≤ ((Devm.getStor spendPre
            sevm.currentTarget).get _).toNat
          rw [storageS]
          exact covered) burnLookup spendTail spendRun
    have moveB : ∀ {offset : Nat} {w : B256}, 896 ≤ offset →
        offset + 32 ≤ (Blanc.ProrataWethVault.balanceWord * 32).toNat →
        MemWordAt entry offset w → MemWordAt burnPre offset w := by
      intro offset w above below window
      have scratch : (Blanc.ProrataWethVault.scratchWord * 32).toNat = 800 := by
        decide +kernel
      have allowance :
          (Blanc.ProrataWethVault.allowanceWord * 32).toNat = 1248 := by
        decide +kernel
      have balance : (Blanc.ProrataWethVault.balanceWord * 32).toNat = 1216 :=
        by decide +kernel
      exact carryB (by omega) (Or.inr (by omega)) (Or.inl (by omega))
        (moveS (move4 (Or.inl below) window))
    exact outboundBurn_revert configB
      (moveB sharesAbove sharesBelow sharesWindow)
      (moveB assetsAbove assetsBelow assetsWindow)
      (moveB (by decide +kernel) supplyMiss supplyWindow)
      (moveB (by decide +kernel) receiverMiss receiverWindow)
      (by omega) receiverValid sharesLe burnRun

end

private theorem vaultFuncs_member {i : Nat} {entry : B256 × Func}
    (lookup : Blanc.ProrataWethVault.vaultFuncs[i]? = some entry) :
    entry ∈ Blanc.ProrataWethVault.vaultFuncs :=
  List.mem_of_getElem? lookup

private theorem vault_withdrawAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.withdrawAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.withdrawAfterQuote := rfl

private theorem vault_redeemAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.redeemAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.redeemAfterQuote := rfl

private theorem vault_withdrawBurn_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.withdrawBurnSlot]? =
      some (Blanc.ProrataWethVault.finishOutbound
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord)
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.amountWord)
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord)) :=
  rfl

private theorem vault_redeemBurn_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.redeemBurnSlot]? =
      some (Blanc.ProrataWethVault.finishOutbound
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.amountWord)
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord)
        (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord)) :=
  rfl

/-- The outbound entry along an avoiding walk: the three arguments are staged,
the booked WETH balance and the share supply are read at their pre-state
values, and the stable-supply guard passes. -/
theorem outboundEntry_avoiding {fs : List Func} {sevm : Sevm}
    {pre bodyPre : Devm} {out : Execution} {arithmetic : Func}
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (entryState : pre.state = bodyPre.state)
    (entryMemory : pre.memory = bodyPre.memory)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre
      (Blanc.arg 0 +++ mstoreAt Blanc.ProrataWethVault.amountWord +++
        Blanc.arg 1 +++ mstoreAt Blanc.ProrataWethVault.receiverWord +++
        Blanc.arg 2 +++ mstoreAt Blanc.ProrataWethVault.ownerWord +++
        Blanc.ProrataWethVault.snapshotQuoteState arithmetic) out) :
    ∃ quotePre : Devm,
      Mem.Wf quotePre.memory ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.amountWord * 32).toNat
        (Sevm.argWord sevm 0) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.receiverWord * 32).toNat
        (Sevm.argWord sevm 1) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.ownerWord * 32).toNat
        (Sevm.argWord sevm 2) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.assetsWord * 32).toNat
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.supplyWord * 32).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot) ∧
      Devm.getStor quotePre = Devm.getStor pre ∧
      DirectWethConfiguration sevm.currentTarget sevm quotePre ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm quotePre arithmetic
        out := by
  have config : DirectWethConfiguration sevm.currentTarget sevm pre :=
    stable.configuration rfl rfl
  obtain ⟨a1, amountArg, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a2, amountStore, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a3, receiverArg, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a4, receiverStore, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a5, ownerArg, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a6, ownerStore, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have argSource : Func.Run ([] : List Func) sevm bodyPre
      (Blanc.arg 0 +++ mstoreAt Blanc.ProrataWethVault.amountWord +++
        Blanc.arg 1 +++ mstoreAt Blanc.ProrataWethVault.receiverWord +++
        Blanc.arg 2 +++ mstoreAt Blanc.ProrataWethVault.ownerWord +++
        Func.stop) a6 :=
    Func.Run.prepend_line amountArg (Func.Run.prepend_line amountStore
      (Func.Run.prepend_line receiverArg (Func.Run.prepend_line receiverStore
        (Func.Run.prepend_line ownerArg (Func.Run.prepend_line ownerStore
          (Func.Run.last rfl))))))
  have bodyWf : Mem.Wf bodyPre.memory := entryMemory ▸ memoryWf
  obtain ⟨readPre, -, readWf, readReads, argState, -, stopRun⟩ :=
    Blanc.ProrataWethVault.outboundArgs_trace (R := Func.Run) bodyWf
      (selfReads bodyPre) nil_pref argSource
  obtain rfl := Func.Run.stop_inv stopRun
  have readState : pre.state = a6.state := entryState.trans argState
  have readStorage : Devm.getStor a6 = Devm.getStor pre :=
    funext (getStor_eq_of_state_eq readState.symm)
  have amountWindow : MemWordAt a6
      (Blanc.ProrataWethVault.amountWord * 32).toNat (Sevm.argWord sevm 0) :=
    MemWordAt.of_memImage ⟨readWf, readReads⟩ (sliceBytes_of_toB256
      (Blanc.ProrataWethVault.outboundArgImage_amount _ _ _ _))
  have receiverWindow : MemWordAt a6
      (Blanc.ProrataWethVault.receiverWord * 32).toNat (Sevm.argWord sevm 1) :=
    MemWordAt.of_memImage ⟨readWf, readReads⟩ (sliceBytes_of_toB256
      (Blanc.ProrataWethVault.outboundArgImage_receiver _ _ _ _))
  have ownerWindow : MemWordAt a6
      (Blanc.ProrataWethVault.ownerWord * 32).toNat (Sevm.argWord sevm 2) :=
    MemWordAt.of_memImage ⟨readWf, readReads⟩ (sliceBytes_of_toB256
      (Blanc.ProrataWethVault.outboundArgImage_owner _ _ _ _))
  have supplyStable : (Devm.getStorVal a6 sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN := by
    change ((Devm.getStor a6 sevm.currentTarget).get
      Blanc.ProrataWethVault.supplySlot).toNat ≤ _
    rw [readStorage]
    exact stable.backed.2.1
  obtain ⟨quotePre, quoteWf, assetsWindow, supplyWindow, carry, quoteStorage,
      quoteConfig, run⟩ :=
    snapshotQuoteState_avoiding (config.of_state_eq' readState) readWf
      supplyStable run
  refine ⟨quotePre, quoteWf,
    carry (by decide +kernel) (by decide +kernel) amountWindow,
    carry (by decide +kernel) (by decide +kernel) receiverWindow,
    carry (by decide +kernel) (by decide +kernel) ownerWindow, ?_, ?_,
    quoteStorage.trans readStorage, quoteConfig, run⟩
  · have assetsEq : (a6.state.getStor wethAccount).get
        sevm.currentTarget.toB256 =
        (pre.state.getStor wethAccount).get sevm.currentTarget.toB256 := by
      rw [readState]
    rw [← assetsEq]
    exact assetsWindow
  · have supplyEq : Devm.getStorVal a6 sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot =
        Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot := by
      change (Devm.getStor a6 sevm.currentTarget).get _ =
        (Devm.getStor pre sevm.currentTarget).get _
      rw [readStorage]
    rw [← supplyEq]
    exact supplyWindow

/-- A booked owner balance is at most the share supply on a conserved
ledger. -/
private theorem ownerBalance_le_supply {sevm : Sevm} {pre : Devm} {owner : B256}
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget))
    (ownerValid : ValidAdr owner) :
    (Devm.getStorVal pre sevm.currentTarget owner).toNat ≤
      (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat := by
  obtain ⟨ownerAdr, rfl⟩ := ownerValid
  exact conserved.le_supply ownerAdr

/-- **`withdraw` up to `maxWithdraw` does not take a vault revert.**  At a
stable pair state, a `withdraw(assets, receiver, owner)` frame with zero value,
a complete static ABI head, a nonzero caller, canonical nonzero receiver and
owner, `assets ≤ maxWithdraw(owner)`, and share authorization (the caller is
the owner, or the owner-caller allowance key is collision-free and the
allowance covers the quoted burn) reverts only through a refused WETH child
(`balanceOf` or `transfer`). -/
theorem withdraw_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 3)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (ownerValid : ValidAdr (Sevm.argWord sevm 2))
    (ownerNonzero : Sevm.argWord sevm 2 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxWithdrawViewN
          (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget
            Blanc.ProrataWethVault.supplySlot).toNat)
    (authorized :
      sevm.caller.toB256 = Sevm.argWord sevm 2 ∨
        (¬ ValidAdr (Blanc.ProrataWethVault.allowanceKey
            (Sevm.argWord sevm 2) sevm.caller.toB256) ∧
          Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
              sevm.caller.toB256 ≠ Blanc.ProrataWethVault.supplySlot ∧
          Blanc.ProrataWethVault.previewWithdrawN (Sevm.argWord sevm 0).toNat
              ((pre.state.getStor wethAccount).get
                sevm.currentTarget.toB256).toNat
              (Devm.getStorVal pre sevm.currentTarget
                Blanc.ProrataWethVault.supplySlot).toNat ≤
            (Devm.getStorVal pre sevm.currentTarget
              (Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
                sevm.caller.toB256)).toNat))
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  have stableSupply : (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN := stable.backed.2.1
  have conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget) := stable.backed.1
  have balanceLe := ownerBalance_le_supply conserved ownerValid
  have assetsWord : ((pre.state.getStor wethAccount).get
      sevm.currentTarget.toB256).toNat ≤ maxWordN := by
    have := B256.toNat_lt ((pre.state.getStor wethAccount).get
      sevm.currentTarget.toB256)
    unfold maxWordN wordModulusN
    omega
  rw [Blanc.ProrataWethVault.maxWithdrawViewN_eq_of_stable stableSupply
    balanceLe assetsWord] at withinMax
  -- The owner-balance guard's revert arm is refuted by this fact: the exact
  -- ceiling burn is within the owner's booked shares.
  have covered :=
    (Blanc.ProrataWethVault.le_maxWithdrawN_iff _ _ _ _).mp withinMax
  have quoteFits : Blanc.ProrataWethVault.previewWithdrawN
      (Sevm.argWord sevm 0).toNat
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat
      (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat < wordModulusN :=
    Nat.lt_of_le_of_lt covered (B256.toNat_lt _)
  refine vault_revert_visits_of_body selectorEq
    (vaultFuncs_member (i := 17) rfl) valueZero argsPresent walk ?_
  intro bodyPre entryState entryMemory run
  unfold Blanc.ProrataWethVault.withdraw at run
  obtain ⟨quotePre, quoteWf, amountWindow, receiverWindow, ownerWindow,
      assetsWindow, supplyWindow, quoteStorage, quoteConfig, run⟩ :=
    outboundEntry_avoiding stable memoryWf entryState entryMemory run
  obtain ⟨afterPre, afterImage, afterStack, afterMemImage, afterFrame,
      afterQuiet, run⟩ :=
    Blanc.ProrataWethVault.withdrawQuote_avoiding quoteWf (selfReads quotePre)
      (MemWordAt.self_toB256 amountWindow) (MemWordAt.self_toB256 assetsWindow)
      (MemWordAt.self_toB256 supplyWindow) stableSupply nil_pref
      vault_withdrawAfterQuote_lookup run quoteFits
  have scratchEnd : Blanc.ProrataWethVault.arithmeticScratchEnd = 896 := by
    decide +kernel
  unfold Blanc.ProrataWethVault.withdrawAfterQuote at run
  obtain ⟨guardPre, storeRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨guardStack, guardWf, quoteWindow, storeMiss, storeState⟩ :=
    mstoreAt_window afterStack afterMemImage.1 storeRun
  have move : ∀ {offset : Nat} {w : B256}, 896 ≤ offset →
      (offset + 32 ≤ (Blanc.ProrataWethVault.quoteWord * 32).toNat ∨
        (Blanc.ProrataWethVault.quoteWord * 32).toNat + 32 ≤ offset) →
      MemWordAt quotePre offset w → MemWordAt guardPre offset w := by
    intro offset w above miss window
    exact storeMiss miss (window.of_wordFrame (selfReads quotePre)
      afterMemImage afterFrame (by rw [scratchEnd]; exact above))
  have guardStorage : Devm.getStor guardPre = Devm.getStor pre :=
    (funext (getStor_eq_of_state_eq (afterQuiet.1.trans storeState))).symm.trans
      quoteStorage
  have quoteNat := B256.toNat_toB256_of_lt quoteFits
  refine outboundGuardedTail_revert
    (quoteConfig.of_state_eq' (afterQuiet.1.trans storeState)) guardWf
    (move (by decide +kernel) (Or.inl (by decide +kernel)) receiverWindow)
    (move (by decide +kernel) (Or.inl (by decide +kernel)) ownerWindow)
    (move (by decide +kernel) (Or.inr (by decide +kernel)) supplyWindow)
    quoteWindow
    (move (by decide +kernel) (Or.inl (by decide +kernel)) amountWindow)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    callerNonzero receiverValid receiverNonzero ownerValid ownerNonzero
    ?_ ?_ ?_ ?_ vault_withdrawBurn_lookup guardStack run
  · change _ ≤ ((Devm.getStor guardPre sevm.currentTarget).get _).toNat
    rw [guardStorage, quoteNat]
    exact covered
  · rcases authorized with ownerCaller | ⟨notAddress, notSupply, allowed⟩
    · exact Or.inl ownerCaller
    · refine Or.inr ⟨notAddress, notSupply, ?_⟩
      change _ ≤ ((Devm.getStor guardPre sevm.currentTarget).get _).toNat
      rw [guardStorage, quoteNat]
      exact allowed
  · rw [guardStorage]
    exact conserved
  · change _ = (Devm.getStor guardPre sevm.currentTarget).get _
    rw [guardStorage]
    rfl


/-- **`redeem` up to `maxRedeem` does not take a vault revert.**  As for
`withdraw`, with `shares ≤ maxRedeem(owner)` and the allowance covering the
shares themselves. -/
theorem redeem_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 3)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (ownerValid : ValidAdr (Sevm.argWord sevm 2))
    (ownerNonzero : Sevm.argWord sevm 2 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxRedeemN
          (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat)
    (authorized :
      sevm.caller.toB256 = Sevm.argWord sevm 2 ∨
        (¬ ValidAdr (Blanc.ProrataWethVault.allowanceKey
            (Sevm.argWord sevm 2) sevm.caller.toB256) ∧
          Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
              sevm.caller.toB256 ≠ Blanc.ProrataWethVault.supplySlot ∧
          (Sevm.argWord sevm 0).toNat ≤
            (Devm.getStorVal pre sevm.currentTarget
              (Blanc.ProrataWethVault.allowanceKey (Sevm.argWord sevm 2)
                sevm.caller.toB256)).toNat))
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  have stableSupply : (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN := stable.backed.2.1
  have conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget) := stable.backed.1
  have balanceLe := ownerBalance_le_supply conserved ownerValid
  -- The owner-balance guard's revert arm is refuted by `withinMax` itself:
  -- `maxRedeem` is the owner's booked balance.
  have covered : (Sevm.argWord sevm 0).toNat ≤
      (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat :=
    withinMax
  have quoteFits : Blanc.ProrataWethVault.previewRedeemN
      (Sevm.argWord sevm 0).toNat
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat
      (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat < wordModulusN := by
    have mono : Blanc.ProrataWethVault.previewRedeemN
        (Sevm.argWord sevm 0).toNat
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxWithdrawN
          (Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 2)).toNat
          ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget
            Blanc.ProrataWethVault.supplySlot).toNat := by
      unfold Blanc.ProrataWethVault.previewRedeemN
        Blanc.ProrataWethVault.maxWithdrawN
        Blanc.ProrataWethVault.convertToAssetsN
      exact Nat.div_le_div_right (Nat.mul_le_mul_right _ covered)
    exact Nat.lt_of_le_of_lt (mono.trans
      (Blanc.ProrataWethVault.maxWithdrawN_le_assets balanceLe))
      (B256.toNat_lt _)
  refine vault_revert_visits_of_body selectorEq
    (vaultFuncs_member (i := 18) rfl) valueZero argsPresent walk ?_
  intro bodyPre entryState entryMemory run
  unfold Blanc.ProrataWethVault.redeem at run
  obtain ⟨quotePre, quoteWf, amountWindow, receiverWindow, ownerWindow,
      assetsWindow, supplyWindow, quoteStorage, quoteConfig, run⟩ :=
    outboundEntry_avoiding stable memoryWf entryState entryMemory run
  obtain ⟨afterPre, afterImage, afterStack, afterMemImage, afterFrame,
      afterQuiet, run⟩ :=
    Blanc.ProrataWethVault.redeemQuote_avoiding quoteWf (selfReads quotePre)
      (MemWordAt.self_toB256 amountWindow) (MemWordAt.self_toB256 assetsWindow)
      (MemWordAt.self_toB256 supplyWindow) stableSupply nil_pref
      vault_redeemAfterQuote_lookup run quoteFits
  have scratchEnd : Blanc.ProrataWethVault.arithmeticScratchEnd = 896 := by
    decide +kernel
  unfold Blanc.ProrataWethVault.redeemAfterQuote at run
  obtain ⟨guardPre, storeRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨guardStack, guardWf, quoteWindow, storeMiss, storeState⟩ :=
    mstoreAt_window afterStack afterMemImage.1 storeRun
  have move : ∀ {offset : Nat} {w : B256}, 896 ≤ offset →
      (offset + 32 ≤ (Blanc.ProrataWethVault.quoteWord * 32).toNat ∨
        (Blanc.ProrataWethVault.quoteWord * 32).toNat + 32 ≤ offset) →
      MemWordAt quotePre offset w → MemWordAt guardPre offset w := by
    intro offset w above miss window
    exact storeMiss miss (window.of_wordFrame (selfReads quotePre)
      afterMemImage afterFrame (by rw [scratchEnd]; exact above))
  have guardStorage : Devm.getStor guardPre = Devm.getStor pre :=
    (funext (getStor_eq_of_state_eq (afterQuiet.1.trans storeState))).symm.trans
      quoteStorage
  refine outboundGuardedTail_revert
    (quoteConfig.of_state_eq' (afterQuiet.1.trans storeState)) guardWf
    (move (by decide +kernel) (Or.inl (by decide +kernel)) receiverWindow)
    (move (by decide +kernel) (Or.inl (by decide +kernel)) ownerWindow)
    (move (by decide +kernel) (Or.inr (by decide +kernel)) supplyWindow)
    (move (by decide +kernel) (Or.inl (by decide +kernel)) amountWindow)
    quoteWindow
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
    callerNonzero receiverValid receiverNonzero ownerValid ownerNonzero
    ?_ ?_ ?_ ?_ vault_redeemBurn_lookup guardStack run
  · change _ ≤ ((Devm.getStor guardPre sevm.currentTarget).get _).toNat
    rw [guardStorage]
    exact covered
  · rcases authorized with ownerCaller | ⟨notAddress, notSupply, allowed⟩
    · exact Or.inl ownerCaller
    · refine Or.inr ⟨notAddress, notSupply, ?_⟩
      change _ ≤ ((Devm.getStor guardPre sevm.currentTarget).get _).toNat
      rw [guardStorage]
      exact allowed
  · rw [guardStorage]
    exact conserved
  · change _ = (Devm.getStor guardPre sevm.currentTarget).get _
    rw [guardStorage]
    rfl

end Blanc.Composition.ProrataWethVault
