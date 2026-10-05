import Blanc.Lift.UniswapV2Pair.SwapFront
import Blanc.Lift.UniswapV2Pair.SafeTransferWalk

/-! The swap's optimistic transfers (`t_08bf_c4..t_08e1_c4`): each nonzero output amount calls
the shared `_safeTransfer` helper `t_1fdb_c57` at the CURRENT free pointer, consumed through the
helper's pointer-generic public API (`safeTransfer_dynamicReturned_inv`). The first transfer
runs at the PC0 pointer 128; the second runs at the pointer the first one moved. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The free pointer an actual `_safeTransfer` leaves: its 164-byte staging area, then the
helper's optional reply array. -/
def swapMovedPointer (p : B256) (reply : Bytes) : B256 :=
  if reply = [] then p + 164 else p + 164 + ((reply.length.toB256 + 63) &&& ~~~31)

/-- Under the CALL reply bound the moved pointer is the natural allocation.
(`swapTransferMemory` now lives in `SafeTransferWalk`, seen via import.) -/
theorem swapMovedPointer_layout {p : B256} {reply : Bytes}
    (short : reply.length < 2 ^ 160) (room : p.toNat + 2 ^ 161 < 2 ^ 256) :
    (swapMovedPointer p reply).toNat =
      p.toNat + 164 + (if reply = [] then 0 else 32 * ((reply.length + 63) / 32)) ∧
    p.toNat + 164 ≤ (swapMovedPointer p reply).toNat ∧
    (swapMovedPointer p reply).toNat ≤ p.toNat + 164 + reply.length + 63 := by
  have lenWidth : reply.length < 2 ^ 256 := by omega
  have sumWidth : reply.length + 63 < 2 ^ 256 := by omega
  have startWidth : p.toNat + 164 < 2 ^ 256 := by omega
  have startNat : (p + 164).toNat = p.toNat + 164 := by
    rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl, Nat.lo_eq_of_lt startWidth]
  have sumNat : (reply.length.toB256 + (63 : B256)).toNat = reply.length + 63 := by
    rw [B256.toNat_add, B256.toNat_toB256_of_lt lenWidth,
      show (63 : B256).toNat = 63 from rfl, Nat.lo_eq_of_lt sumWidth]
  have maskNat : ((reply.length.toB256 + (63 : B256)) &&& ~~~31).toNat =
      32 * ((reply.length + 63) / 32) := by
    rw [B256.toNat_and, sumNat,
      show (~~~ (31 : B256)).toNat = 2 ^ 256 - 32 from rfl,
      Nat.and_mask32 sumWidth]
  have division := Nat.mod_add_div (reply.length + 63) 32
  have remainder : (reply.length + 63) % 32 < 32 := Nat.mod_lt _ (by decide)
  have roundedWidth : p.toNat + 164 + 32 * ((reply.length + 63) / 32) < 2 ^ 256 := by omega
  have pointerNat : (p + 164 + ((reply.length.toB256 + 63) &&& ~~~31)).toNat =
      p.toNat + 164 + 32 * ((reply.length + 63) / 32) := by
    rw [B256.toNat_add, startNat, maskNat, Nat.lo_eq_of_lt roundedWidth]
  by_cases empty : reply = []
  · simp only [swapMovedPointer, empty, ite_true, startNat, Nat.add_zero]
    exact ⟨True.intro, Nat.le_refl _, by omega⟩
  · simp only [swapMovedPointer, ite_eq_right empty, pointerNat]
    exact ⟨True.intro, by omega, by omega⟩

/-- One actual optimistic transfer CALL of the helper at pointer `p`, with its canonical
calldata, its full reply and the helper's derived optional-bool acceptance. -/
def SwapTransferCall (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (L : List B256) (M : Mem)
    (p amount toWord token rho : B256) (d : Devm) : Prop :=
  (∃ forwarded callGas, StepIn D sevm
    (St b (forwarded :: (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      0 :: (p + 164) :: 68 :: (p + 164) :: 0 :: (68 + (p + 164)) ::
      (token &&& 0xffffffffffffffffffffffffffffffffffffffff) ::
      96 :: 0 :: amount :: toWord :: token :: rho :: L)
      (safeTransfer_dynamicCallMemory M p amount toWord) callGas) (.exec .call) d) ∧
  ((safeTransfer_dynamicCallMemory M p amount toWord).read (p + 164).toNat 68).1 =
    abiSelectorBytes 0xa9059cbb ++
      ((0xffffffffffffffffffffffffffffffffffffffff : B256) &&& toWord).toBytes ++ amount.toBytes ∧
  d.memory = safeTransfer_dynamicCallMemory M p amount toWord ∧ d.output = b.output ∧
  d.returnData.length < 2 ^ 256 ∧
  (d.returnData = [] ∨ (32 ≤ d.returnData.length ∧
    Bytes.toB256 (d.returnData.sliceD 0 32 0) ≠ 0))

/-- A returned helper at pointer `p`: its actual CALL, the returned state and the free-pointer
carrier at the moved pointer. -/
theorem swapTransfer_returned_inv {D : Exec.Deriv} {sevm : Sevm} {b out : Devm}
    {L : List B256} {M : Mem} {G : Nat} {p amount toWord token rho : B256} {n : Nat}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunP (StepIn D) cert.prog sevm
      (St b (amount :: toWord :: token :: rho :: L) M G) t_1fdb_c57 (.returned out)) :
    ∃ d residual, SwapTransferCall D sevm b L M p amount toWord token rho d ∧
      out = St d L (swapTransferMemory M p amount toWord d.returnData) residual ∧
      ∃ n', PtrMem (swapMovedPointer p d.returnData) n'
        (swapTransferMemory M p amount toWord d.returnData) := by
  obtain ⟨_, _, d', _, _, _, memory', _, _, ptr', _⟩ :=
    safeTransfer_dynamicCall_post_inv StepIn.toRun fork mem lower width
      (by decide : 71 ∉ []) (by decide : 16 ∉ []) (by decide : 17 ∉ [])
      ((SFunc.runP_iff_runCutP_nil (P := StepIn D)).mp run)
  rw [memory'] at ptr'
  obtain ⟨forwarded, callGas, d, residual, step, _, memory, output, replyWidth, accepted, returned⟩ :=
    safeTransfer_dynamicReturned_inv StepIn.toRun fork mem lower width run
  have calldata := safeTransfer_dynamicCall_data
    (amount := amount) (toWord := toWord) mem.wf lower (by omega : p.toNat + 164 < 2 ^ 256)
  refine ⟨d, residual, ⟨⟨forwarded, callGas, step⟩, calldata, memory, output, replyWidth, accepted⟩,
    ?_, ?_⟩
  · rw [returned, memory]
    by_cases empty : d.returnData = []
    · simp only [swapTransferMemory, empty, ite_true]
    · simp only [swapTransferMemory, ite_eq_right empty]
  · have nat164 : (p + 164).toNat = p.toNat + 164 := by
      rw [B256.toNat_add, show (164 : B256).toNat = 164 from rfl, Nat.lo_eq_of_lt (by omega)]
    by_cases empty : d.returnData = []
    · simp only [swapMovedPointer, swapTransferMemory, empty, ite_true]
      exact ⟨_, ptr'⟩
    · simp only [swapMovedPointer, swapTransferMemory, ite_eq_right empty]
      exact ⟨_, (Blanc.Lift.bytesArrayMemory_image (bytes := d.returnData) ptr'
        (by rw [nat164]; omega) (by rw [nat164]; omega) (by rw [nat164]; omega)).1⟩

/-- A literal transfer site: the helper is entered with the site's continuation, returns at
the moved pointer, and the run continues there with the caller's locals. -/
theorem swapTransferSite_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {L : List B256} {M : Mem} {G : Nat} {w p amount toWord token rho : B256} {n : Nat}
    {k : SFunc} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (w :: amount :: toWord :: token :: rho :: L) M G) (.callNext 57 k) seg) :
    ∃ d residual, SwapTransferCall D sevm b L M p amount toWord token rho d ∧
      (∃ n', PtrMem (swapMovedPointer p d.returnData) n'
        (swapTransferMemory M p amount toWord d.returnData)) ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm []
        (St d L (swapTransferMemory M p amount toWord d.returnData) residual) k seg := by
  cases run with
  | callHalt d lookup pop callee =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    exact False.elim (callee.not_halted_entry (S := [16,17,57,71])
      (by decide) (by decide : 57 ∈ [16,17,57,71]) (by rfl : cert.prog[57]? = some t_1fdb_c57) rfl)
  | callRet d lookup pop callee continuation =>
    change some t_1fdb_c57 = _ at lookup
    cases lookup
    obtain ⟨d, residual, call, returned, ptr⟩ :=
      swapTransfer_returned_inv fork mem lower width ((St.of_pop1 pop).2 ▸ callee)
    rw [returned] at continuation
    exact ⟨d, residual, call, ptr, continuation⟩

/-- An optional optimistic transfer as actually executed: a zero amount skips the helper and
keeps world, memory and pointer; a nonzero amount is one actual helper CALL. -/
def SwapTransferOpt (D : Exec.Deriv) (sevm : Sevm) (b : Devm) (L : List B256) (M : Mem)
    (p amount toWord token rho : B256) (b' : Devm) (M' : Mem) (p' : B256) : Prop :=
  (amount = 0 ∧ b' = b ∧ M' = M ∧ p' = p) ∨
  (amount ≠ 0 ∧ SwapTransferCall D sevm b L M p amount toWord token rho b' ∧
    M' = swapTransferMemory M p amount toWord b'.returnData ∧
    p' = swapMovedPointer p b'.returnData)

/-- An actual optimistic-transfer CALL returns fewer than `2^160` bytes: the Jaune
operand-derived reply bound (`Jaune.call_returnData_length_lt_two_pow_160_of_input_size`,
registered in `docs/COMMON_API.md`) applied to the call's 68-byte input. -/
theorem swapTransferCall_replyShort {D : Exec.Deriv} {sevm : Sevm} {b : Devm}
    {L : List B256} {M : Mem} {p amount toWord token rho : B256} {d : Devm}
    (fork : CoveredFork sevm.benvStat.fork)
    (call : SwapTransferCall D sevm b L M p amount toWord token rho d) :
    d.returnData.length < 2 ^ 160 := by
  obtain ⟨_, _, step⟩ := call.1
  exact Jaune.call_returnData_length_lt_two_pow_160_of_input_size
    (StepIn.toRun step) rfl fork.rules_stateGas_none
    (by decide : (68 : B256).toNat < 2 ^ 160)

/-- Both optimistic transfers, from the transfer branch to the callback branch `t_08e1_c4`.
The second transfer runs at the pointer the first one moved; each taken transfer's reply
bound (below `2^160` bytes) is derived from its own actual 68-byte CALL. -/
theorem swapTransfers_inv {D : Exec.Deriv} {sevm : Sevm} {b : Devm} {R : List B256}
    {M : Mem} {G : Nat} {n : Nat} {t1 t0 r1 r0 len start toWord a1 a0 ρ : B256} {seg : Seg}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 n M)
    (run : SFunc.RunCutP (StepIn D) cert.prog sevm []
      (St b (t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R) M G)
      t_08bf_c4 seg) :
    let L := t1 :: t0 :: 0 :: 0 :: r1 :: r0 :: len :: start :: toWord :: a1 :: a0 :: ρ :: R
    ∃ (b1 : Devm) (M1 : Mem) (p1 : B256) (b2 : Devm) (M2 : Mem) (p2 : B256) (n2 gas : Nat),
      SwapTransferOpt D sevm b L M 128 a0 toWord t0 0x8d0 b1 M1 p1 ∧
      SwapTransferOpt D sevm b1 L M1 p1 a1 toWord t1 0x8e1 b2 M2 p2 ∧
      PtrMem p2 n2 M2 ∧ 128 ≤ p2.toNat ∧ p2.toNat < 2 ^ 162 ∧
      SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b2 L M2 gas) t_08e1_c4 seg := by
  intro L
  have shortOf : ∀ {b' : Devm} {L' : List B256} {M' : Mem} {p amount tw token rho : B256} {d : Devm},
      SwapTransferCall D sevm b' L' M' p amount tw token rho d → d.returnData.length < 2 ^ 160 := by
    intro b' L' M' p amount tw token rho d call
    exact swapTransferCall_replyShort fork call
  -- the second site, from any pointer with room
  have second : ∀ {b1 : Devm} {M1 : Mem} {p1 : B256} {n1 G1 : Nat},
      PtrMem p1 n1 M1 → 128 ≤ p1.toNat → p1.toNat < 2 ^ 161 →
      SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b1 L M1 G1) t_08d0_c4 seg →
      ∃ (b2 : Devm) (M2 : Mem) (p2 : B256) (n2 gas : Nat),
        SwapTransferOpt D sevm b1 L M1 p1 a1 toWord t1 0x8e1 b2 M2 p2 ∧
        PtrMem p2 n2 M2 ∧ 128 ≤ p2.toNat ∧ p2.toNat < 2 ^ 162 ∧
        SFunc.RunCutP (StepIn D) cert.prog sevm [] (St b2 L M2 gas) t_08e1_c4 seg := by
    intro b1 M1 p1 n1 G1 mem1 lower1 upper1 run
    unfold t_08d0_c4 at run
    obtain ⟨_, run⟩ := ric_destP run
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    rcases ric_branchP run with ⟨zero, _, run⟩ | ⟨skip, gas, run⟩
    · have nonzero : a1 ≠ 0 := by
        intro h
        rw [h] at zero
        exact absurd zero (by decide)
      unfold t_08d7_c4 at run
      obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
      obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
      obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
      obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
      obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
      simp only [show Bytes.toB256 [0x08, 0xe1] = (0x8e1 : B256) from rfl] at run
      obtain ⟨d, residual, call, ⟨n2, ptr⟩, cont⟩ :=
        swapTransferSite_inv fork mem1 lower1 (by omega) run
      have sh := shortOf call
      have layout := swapMovedPointer_layout sh (by omega : p1.toNat + 2 ^ 161 < 2 ^ 256)
      exact ⟨d, _, _, n2, residual, Or.inr ⟨nonzero, call, rfl, rfl⟩, ptr,
        by omega, by omega, cont⟩
    · have zero : a1 = 0 := eq_zero_of_iszero_ne_zero skip
      exact ⟨b1, M1, p1, n1, gas, Or.inl ⟨zero, rfl, rfl, rfl⟩, mem1, lower1, by omega, run⟩
  unfold t_08bf_c4 at run
  obtain ⟨_, run⟩ := ric_destP run
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun hs)
  obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
  rcases ric_branchP run with ⟨zero, _, run⟩ | ⟨skip, gas, run⟩
  · have nonzero : a0 ≠ 0 := by
      intro h
      rw [h] at zero
      exact absurd zero (by decide)
    unfold t_08c6_c4 at run
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun hs)
    obtain ⟨_, hs, run⟩ := ric_nextP run; obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun hs)
    simp only [show Bytes.toB256 [0x08, 0xd0] = (0x8d0 : B256) from rfl] at run
    obtain ⟨d, residual, call, ⟨n1, ptr⟩, cont⟩ :=
      swapTransferSite_inv fork mem (by decide) (by decide) run
    have sh := shortOf call
    have n128 : (128 : B256).toNat = 128 := rfl
    have layout := swapMovedPointer_layout sh (by decide : (128 : B256).toNat + 2 ^ 161 < 2 ^ 256)
    obtain ⟨b2, M2, p2, n2, gas2, opt, ptr2, lower2, upper2, cont2⟩ :=
      second ptr (by omega) (by omega) cont
    exact ⟨d, _, _, b2, M2, p2, n2, gas2, Or.inr ⟨nonzero, call, rfl, rfl⟩, opt, ptr2, lower2,
      upper2, cont2⟩
  · have zero : a0 = 0 := eq_zero_of_iszero_ne_zero skip
    obtain ⟨b2, M2, p2, n2, gas2, opt, ptr2, lower2, upper2, cont2⟩ :=
      second mem (by decide) (by decide) run
    exact ⟨b, M, 128, b2, M2, p2, n2, gas2, Or.inl ⟨zero, rfl, rfl, rfl⟩, opt, ptr2, lower2,
      upper2, cont2⟩

end Blanc.Lift.UniswapV2Pair
