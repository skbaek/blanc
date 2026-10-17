import Blanc.Lift.Curve3Pool.Walk.Quiet

/-!
# Safety: the admin functions without an external call, inverted

Each segment inverts one body inside entry 0 from the dispatcher's hand-off `quietSt` (empty
stack, the prologue's memory) to its `STOP`: a successful halt is the model's step on the decoded
call (`QuietSafe`). The kit: `ric_vyNonpayable`, `ric_ownerGuard` (`PUSH1 4 SLOAD CALLER EQ`),
`ric_assertJump`, `ric_vyAddrArg`, the `ri_*` steps, and `QStep` for the storage chain; memory
reads are resolved by `mem_reads`. Bodies (pc of the selector test, body tree): `commit_new_fee`
0x499c `t_49aa_c0`, `apply_new_fee` 0x4a65 `t_4a73_c0`, `revert_new_parameters` 0x4b04
`t_4b12_c0`, `commit_transfer_ownership` 0x4b32 `t_4b40_c0`, `apply_transfer_ownership` 0x4bd3
`t_4be1_c0`, `revert_transfer_ownership` 0x4c57 `t_4c65_c0`, `kill_me` 0x500b `t_5019_c0`,
`unkill_me` 0x5047 `t_5055_c0`. Each is the fall-through arm of its dispatcher test
(`PUSH4 sel PUSH1 0 MLOAD EQ ISZERO PUSH2 next JUMPI`).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

section

variable {sevm : Sevm} {b : Devm} {s : State}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

-- SEGMENT: safeCommitNewFee
theorem safe_commitNewFee (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selCommitNewFee)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_49aa_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .commitNewFee (arg sevm 0) (arg sevm 1) :=
    decodeCall_at (k := 13) rfl hsel hlen
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_49b0_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_iszero s1
  obtain ⟨hdl, G7, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_iszero s1
  obtain ⟨hf0, G13, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_iszero s1
  obtain ⟨hf1, G19, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_timestamp s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_iszero s1
  obtain ⟨hnof, G28, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  have hstatic := ri_sstore_nonstatic hfork s1
  obtain ⟨G41, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G51, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G52, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G53, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G54, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G55, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G56, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G57, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G58, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G59, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G60, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G61, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G62, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G63, rfl⟩ := ri_log2_post s1
  cases run with
  | last hl =>
  cases hl
  clear * - hc hdec hv hown hdl hf0 hf1 hnof hstatic hfork hsel hlen
  have h140 : (Bytes.toB256 [1, 64]).toNat = 320 := by decide
  have h160 : (Bytes.toB256 [1, 96]).toNat = 352 := by decide
  have h180 : (Bytes.toB256 [1, 128]).toNat = 384 := by decide
  have h40 : (Bytes.toB256 [64]).toNat = 64 := by decide
  have hs10 : Bytes.toB256 [10] = adminActionsDeadlineSlot := by decide
  have hs12 : Bytes.toB256 [12] = futureFeeSlot := by decide
  have hs13 : Bytes.toB256 [13] = futureAdminFeeSlot := by decide
  have ha0 : Sevm.dataWord sevm (Bytes.toB256 [4]) = Sevm.argWord sevm 0 := rfl
  have ha1 : Sevm.dataWord sevm (Bytes.toB256 [36]) = Sevm.argWord sevm 1 := by
    show Sevm.dataWord sevm _ = Sevm.dataWord sevm _
    congr 1
  have htopic : Bytes.toB256 [53, 31, 197, 218, 47, 191, 72, 15, 34, 37, 222, 191, 54, 100, 164,
      188, 144, 250, 153, 35, 116, 58, 173, 88, 180, 96, 63, 100, 142, 147, 31, 224] =
      topicCommitNewFee := by decide
  rw [h140, h160, h180, h40, hs10, hs12, hs13, ha0, ha1, htopic]
  rw [hs10] at hdl
  rw [ha0] at hf0
  rw [ha1] at hf1
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  generalize vyMem Mem.empty (Sevm.dataWord sevm 0) = M0 at hwf0 ⊢
  clear h140 h160 h180 h40 hs10 hs12 hs13 ha0 ha1 htopic
  generalize hdw : sevm.benvStat.time + Bytes.toB256 [3, 244, 128] = d
  have hwf2 : Mem.Wf ((M0.write 320 d.toBytes).read 320 32).2 := (hwf0.write _ _).extend _ _
  have hr2 : (((((M0.write 320 d.toBytes).read 320 32).2.write 352 (Sevm.argWord sevm 0).toBytes).write
      384 (Sevm.argWord sevm 1).toBytes).read 320 32).1 = d.toBytes := by
    rw [Mem.read_write_disjoint (hwf2.write _ _) _ _ (.inr (by norm_num)),
      Mem.read_write_disjoint hwf2 _ _ (.inr (by norm_num)), memRead_snd_fst,
      Mem.read_write_word_of_wf hwf0]
  have hr3 : ((((((M0.write 320 d.toBytes).read 320 32).2.write 352 (Sevm.argWord sevm 0).toBytes).write
      384 (Sevm.argWord sevm 1).toBytes).read 320 32).2.read 352 64).1 =
      (Sevm.argWord sevm 0).toBytes ++ (Sevm.argWord sevm 1).toBytes := by
    rw [memRead_snd_fst]
    exact Mem.read_two_word_writes hwf2 352 _ _
  rw [Mem.read_write_word_of_wf hwf0, hr2, hr3, B256.toB256_toBytes]
  have hvN : (quietEnv sevm).value = 0 := by
    show sevm.value.toNat = 0
    rw [hv]; rfl
  have hownN : (quietEnv sevm).caller = s.owner := by
    show sevm.caller.toB256.toNat = s.owner
    rw [hown]; exact hc.abs.owner
  have hdlN : s.adminActionsDeadline = 0 := by
    rw [getStorVal_afterSload] at hdl
    rw [← hc.abs.adminActionsDeadline]
    show (b.getStorVal sevm.currentTarget adminActionsDeadlineSlot).toNat = 0
    rw [eq_zero_of_iszero_ne_zero hdl]; rfl
  have hf0N : arg sevm 0 ≤ maxFee := by
    have h := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hf0)
    have c0 : (Bytes.toB256 [1, 42, 5, 242, 0]).toNat = maxFee := by decide
    rw [c0] at h; exact h
  have hf1N : arg sevm 1 ≤ maxAdminFee := by
    have h := toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero hf1)
    have c1 : (Bytes.toB256 [2, 84, 11, 228, 0]).toNat = maxAdminFee := by decide
    rw [c1] at h; exact h
  have hdN : d.toNat = (quietEnv sevm).time + adminActionsDelay ∧
      (quietEnv sevm).time + adminActionsDelay < wordSize := by
    have hlt := eq_zero_of_iszero_ne_zero hnof
    have hnlt : ¬ (sevm.benvStat.time + Bytes.toB256 [3, 244, 128] < sevm.benvStat.time) := by
      unfold B256.ltCheck at hlt; split at hlt
      · cases hlt
      · assumption
    have hN := (B256.nof_iff_not_add_lt _ _).mpr hnlt
    have c2 : (Bytes.toB256 [3, 244, 128]).toNat = adminActionsDelay := by decide
    rw [c2] at hN
    refine ⟨?_, hN⟩
    rw [← hdw, B256.toNat_add_eq_of_nof _ _ (by rw [B256.Nof, c2]; exact hN), c2]; rfl
  refine ⟨⟨{ s with adminActionsDeadline := d.toNat, futureFee := arg sevm 0, futureAdminFee := arg sevm 1 }, none, [.commitNewFee d.toNat (arg sevm 0) (arg sevm 1)], []⟩,
    ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.commitNewFee, hvN, hownN, hdlN, hf0N, hf1N, chkAdd, hdN.2,
      req, if_true]
    rw [← hdN.1]; rfl
  have hq := ((((((QStep.refl sevm b).sload ownerSlot).sload adminActionsDeadlineSlot).sstore
    adminActionsDeadlineSlot d).sstore futureFeeSlot (Sevm.argWord sevm 0)).sstore
    futureAdminFeeSlot (Sevm.argWord sevm 1))
  refine quietLands_stopLog hq ⟨fun x hx => ?_, fun f hf => ?_⟩ ?_ rfl rfl
  · rw [hdec] at hx
    have h1 := hx .adminActionsDeadline (by simp only [footprint, List.mem_cons, true_or])
    have h2 := hx .futureFee (by simp only [footprint, List.mem_cons, true_or, or_true])
    have h3 := hx .futureAdminFee (by simp only [footprint, List.mem_cons, List.mem_singleton,
      true_or, or_true])
    simp only [Fld.slot] at h1 h2 h3
    rw [Stor.get_set_ne _ h3, Stor.get_set_ne _ h2, Stor.get_set_ne _ h1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl
    · show (((((stor₀).set _ d).set _ _).set _ _).get adminActionsDeadlineSlot).toNat = d.toNat
      rw [Stor.get_set_ne _ (by decide), Stor.get_set_ne _ (by decide), Stor.get_set_self]
    · show (((((stor₀).set _ d).set _ _).set _ _).get futureFeeSlot).toNat = arg sevm 0
      rw [Stor.get_set_ne _ (by decide), Stor.get_set_self]; rfl
    · show (((((stor₀).set _ d).set _ _).set _ _).get futureAdminFeeSlot).toNat = arg sevm 1
      rw [Stor.get_set_self]; rfl
  · simp only [List.map_cons, List.map_nil, eventLog, arg, Jaune.toB256_toNat, word]

-- SEGMENT: safeApplyNewFee
theorem safe_applyNewFee (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selApplyNewFee)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_4a73_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .applyNewFee := decodeCall_at (k := 14) rfl hsel hlen
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_4a79_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_timestamp s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨htm, G9, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_xor s1
  obtain ⟨hnz, G14, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_log1 s1
  cases run with
  | last hl =>
  cases hl
  clear * - hc hdec hv hown htm hnz hfork
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  generalize vyMem Mem.empty (Sevm.dataWord sevm 0) = M0 at hwf0 ⊢
  simp only [show (Bytes.toB256 [1, 64]).toNat = 320 from by decide,
    show (Bytes.toB256 [1, 96]).toNat = 352 from by decide,
    show (Bytes.toB256 [1, 128]).toNat = 384 from by decide,
    show (Bytes.toB256 [1, 160]).toNat = 416 from by decide,
    show (Bytes.toB256 [64]).toNat = 64 from by decide,
    show Bytes.toB256 [10] = adminActionsDeadlineSlot from by decide,
    show Bytes.toB256 [12] = futureFeeSlot from by decide,
    show Bytes.toB256 [13] = futureAdminFeeSlot from by decide,
    show Bytes.toB256 [2] = feeSlot from by decide,
    show Bytes.toB256 [3] = adminFeeSlot from by decide,
    show Bytes.toB256 [0] = 0 from by decide] at htm hnz ⊢
  mem_reads
  simp only [getStorVal_afterSload, getStorVal_afterSstore_self', afterSload_getStor,
    afterSstore_getStor_self, getStorVal_eq_getStor] at htm hnz ⊢
  simp (disch := decide) only [Stor.get_set_ne]
  rw [B256.xor_zero] at hnz
  have hvN : (quietEnv sevm).value = 0 := by
    show sevm.value.toNat = 0
    rw [hv]; rfl
  have hownN : (quietEnv sevm).caller = s.owner := by
    show sevm.caller.toB256.toNat = s.owner
    rw [hown]; exact hc.abs.owner
  have htmN : (quietEnv sevm).time ≥ s.adminActionsDeadline := by
    rw [← hc.abs.adminActionsDeadline]
    exact toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero htm)
  have hnzN : s.adminActionsDeadline ≠ 0 := by
    rw [← hc.abs.adminActionsDeadline]
    intro h0
    exact hnz (B256.toNat_inj _ _ (h0.trans rfl))
  refine ⟨⟨{ s with adminActionsDeadline := 0, fee := s.futureFee, adminFee := s.futureAdminFee },
    none, [.newFee s.futureFee s.futureAdminFee], []⟩, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.applyNewFee, hvN, hownN, htmN, hnzN, req, ite_true,
      ne_eq, not_false_eq_true]
    rfl
  refine quietLands_stopLog (((((((((QStep.refl sevm b).sload ownerSlot).sload
    adminActionsDeadlineSlot).sload adminActionsDeadlineSlot).sstore adminActionsDeadlineSlot 0).sload
    futureFeeSlot).sload futureAdminFeeSlot).sstore feeSlot _).sstore adminFeeSlot _)
    ⟨fun x hx => ?_, fun f hf => ?_⟩ ?_ rfl rfl
  · rw [hdec] at hx
    simp only [footprint, List.mem_cons, List.mem_singleton, forall_eq_or_imp, forall_eq,
      Fld.slot] at hx
    obtain ⟨h1, h2, h3, -⟩ := hx
    rw [Stor.get_set_ne _ h3, Stor.get_set_ne _ h2, Stor.get_set_ne _ h1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl <;>
      simp (disch := decide) only [Fld.Reads, Stor.get_set_ne, Stor.get_set_self]
    · rfl
    · exact hc.abs.futureFee
    · exact hc.abs.futureAdminFee
  · simp only [List.map_cons, List.map_nil, eventLog, word, ← hc.abs.futureFee,
      ← hc.abs.futureAdminFee, Jaune.toB256_toNat]
    rfl

-- SEGMENT: safeRevertNewParameters
theorem safe_revertNewParameters (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selRevertNewParameters)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_4b12_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .revertNewParameters := decodeCall_at (k := 15) rfl hsel hlen
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_4b18_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sstore hfork s1
  cases run with
  | last hl =>
  cases hl
  rw [show Bytes.toB256 [10] = adminActionsDeadlineSlot from by decide,
    show Bytes.toB256 [0] = 0 from by decide]
  refine ⟨⟨{ s with adminActionsDeadline := 0 }, none, [], []⟩, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.revertNewParameters, quietEnv_value hv,
      quietEnv_owner hc hown, req, ite_true]
    rfl
  refine quietLands_stop (((QStep.refl sevm b).sload ownerSlot).sstore adminActionsDeadlineSlot 0)
    ⟨fun x hx => ?_, fun f hf => ?_⟩ rfl rfl rfl
  · rw [hdec] at hx
    simp only [footprint, List.mem_cons, forall_eq_or_imp, Fld.slot] at hx
    rw [Stor.get_set_ne _ hx.1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    simp only [Fld.Reads, Stor.get_set_self]
    rfl

-- SEGMENT: safeRevertTransferOwnership
theorem safe_revertTransferOwnership (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selRevertTransferOwnership)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_4c65_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .revertTransferOwnership := decodeCall_at (k := 18) rfl hsel hlen
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_4c6b_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sstore hfork s1
  cases run with
  | last hl =>
  cases hl
  rw [show Bytes.toB256 [11] = transferOwnershipDeadlineSlot from by decide,
    show Bytes.toB256 [0] = 0 from by decide]
  refine ⟨⟨{ s with transferOwnershipDeadline := 0 }, none, [], []⟩, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.revertTransferOwnership, quietEnv_value hv,
      quietEnv_owner hc hown, req, ite_true]
    rfl
  refine quietLands_stop (((QStep.refl sevm b).sload ownerSlot).sstore
    transferOwnershipDeadlineSlot 0) ⟨fun x hx => ?_, fun f hf => ?_⟩ rfl rfl rfl
  · rw [hdec] at hx
    simp only [footprint, List.mem_cons, forall_eq_or_imp, Fld.slot] at hx
    rw [Stor.get_set_ne _ hx.1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    simp only [Fld.Reads, Stor.get_set_self]
    rfl

-- SEGMENT: safeUnkillMe
theorem safe_unkillMe (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selUnkillMe)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_5055_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .unkillMe := decodeCall_at (k := 23) rfl hsel hlen
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_505b_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sstore hfork s1
  cases run with
  | last hl =>
  cases hl
  rw [show Bytes.toB256 [15] = isKilledSlot from by decide,
    show Bytes.toB256 [0] = boolWord false from by decide]
  refine ⟨⟨{ s with isKilled := false }, none, [], []⟩, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.unkillMe, quietEnv_value hv,
      quietEnv_owner hc hown, req, ite_true]
    rfl
  refine quietLands_stop (((QStep.refl sevm b).sload ownerSlot).sstore
    isKilledSlot (boolWord false)) ⟨fun x hx => ?_, fun f hf => ?_⟩ rfl rfl rfl
  · rw [hdec] at hx
    simp only [footprint, List.mem_cons, forall_eq_or_imp, Fld.slot] at hx
    rw [Stor.get_set_ne _ hx.1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    simp only [Fld.Reads, Stor.get_set_self]

-- SEGMENT: safeKillMe
theorem safe_killMe (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selKillMe)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_5019_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .killMe := decodeCall_at (k := 22) rfl hsel hlen
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_501f_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_timestamp s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_gt s1
  obtain ⟨hkd, G7, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_sstore hfork s1
  cases run with
  | last hl =>
  cases hl
  rw [show Bytes.toB256 [15] = isKilledSlot from by decide,
    show Bytes.toB256 [1] = boolWord true from by decide]
  rw [show Bytes.toB256 [16] = killDeadlineSlot from by decide, getStorVal_afterSload,
    getStorVal_eq_getStor] at hkd
  have hkdN : s.killDeadline > (quietEnv sevm).time := by
    rw [← hc.abs.killDeadline]
    have h := hkd
    unfold B256.gtCheck at h
    split at h
    · rename_i hgt
      exact B256.lt_iff_toNat_lt_toNat.mp hgt
    · exact absurd rfl h
  refine ⟨⟨{ s with isKilled := true }, none, [], []⟩, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.killMe, quietEnv_value hv,
      quietEnv_owner hc hown, hkdN, req, ite_true]
    rfl
  refine quietLands_stop (((QStep.refl sevm b).sload ownerSlot).sload killDeadlineSlot |>.sstore
    isKilledSlot (boolWord true)) ⟨fun x hx => ?_, fun f hf => ?_⟩ rfl rfl rfl
  · rw [hdec] at hx
    simp only [footprint, List.mem_cons, forall_eq_or_imp, Fld.slot] at hx
    rw [Stor.get_set_ne _ hx.1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hf
    subst hf
    simp only [Fld.Reads, Stor.get_set_self]

-- SEGMENT: safeApplyTransferOwnership
theorem safe_applyTransferOwnership (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selApplyTransferOwnership)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_4be1_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .applyTransferOwnership := decodeCall_at (k := 17) rfl hsel hlen
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_4be7_c0) rfl run
  obtain ⟨hown, G2, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_timestamp s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_iszero s1
  obtain ⟨htm, G9, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_xor s1
  obtain ⟨hnz, G14, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_log2_post s1
  cases run with
  | last hl =>
  cases hl
  clear * - hc hdec hv hown htm hnz hfork
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  generalize vyMem Mem.empty (Sevm.dataWord sevm 0) = M0 at hwf0 ⊢
  simp only [show (Bytes.toB256 [1, 64]).toNat = 320 from by decide,
    show (Bytes.toB256 [0]).toNat = 0 from by decide,
    show Bytes.toB256 [11] = transferOwnershipDeadlineSlot from by decide,
    show Bytes.toB256 [14] = futureOwnerSlot from by decide,
    show Bytes.toB256 [4] = ownerSlot from by decide,
    show Bytes.toB256 [0] = 0 from by decide] at htm hnz ⊢
  mem_reads
  simp only [getStorVal_afterSload, afterSload_getStor, afterSstore_getStor_self,
    getStorVal_eq_getStor] at htm hnz ⊢
  simp (disch := decide) only [Stor.get_set_ne]
  rw [B256.xor_zero] at hnz
  have htmN : (quietEnv sevm).time ≥ s.transferOwnershipDeadline := by
    rw [← hc.abs.transferOwnershipDeadline]
    exact toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero htm)
  have hnzN : s.transferOwnershipDeadline ≠ 0 := by
    rw [← hc.abs.transferOwnershipDeadline]
    intro h0
    exact hnz (B256.toNat_inj _ _ (h0.trans rfl))
  refine ⟨⟨{ s with transferOwnershipDeadline := 0, owner := s.futureOwner }, none,
    [.newAdmin s.futureOwner], []⟩, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.applyTransferOwnership, quietEnv_value hv,
      quietEnv_owner hc hown, htmN, hnzN, req, ite_true, ne_eq, not_false_eq_true]
    rfl
  refine quietLands_stopLog (((((((QStep.refl sevm b).sload ownerSlot).sload
    transferOwnershipDeadlineSlot).sload transferOwnershipDeadlineSlot).sstore
    transferOwnershipDeadlineSlot 0).sload futureOwnerSlot).sstore ownerSlot _)
    ⟨fun x hx => ?_, fun f hf => ?_⟩ ?_ rfl rfl
  · rw [hdec] at hx
    simp only [footprint, List.mem_cons, forall_eq_or_imp, Fld.slot] at hx
    obtain ⟨h1, h2, -⟩ := hx
    rw [Stor.get_set_ne _ h2, Stor.get_set_ne _ h1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;>
      simp (disch := decide) only [Fld.Reads, Stor.get_set_ne, Stor.get_set_self]
    · rfl
    · exact hc.abs.futureOwner
  · simp only [List.map_cons, List.map_nil, eventLog, ← hc.abs.futureOwner, Jaune.toB256_toNat]
    rfl

-- SEGMENT: safeCommitTransferOwnership
theorem safe_commitTransferOwnership (hfork : CoveredFork sevm.benvStat.fork)
    (hc : Checkpoint stor₀ s) (hsel : Sevm.selector sevm = selCommitTransferOwnership)
    (hlen : 4 ≤ sevm.data.length) : QuietSafe sevm b s t_4b40_c0 := by
  intro G post run
  have hdec : decodeCall sevm = .commitTransferOwnership (arg sevm 0) :=
    decodeCall_at (k := 16) rfl hsel hlen
  have hM := vyMem_empty_size (Sevm.dataWord sevm 0)
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable (fail := t_4b46_c0) rfl run
  obtain ⟨hcl, G2, run⟩ := ric_vyAddrArg (p := 0x04) (h := 0x4b) (l := 0x5b) (fail := t_4b57_c0)
    rfl (vyMem_reads Mem.wf_empty Mem.reads_empty _) (vyImg_clamps _ _) (by rw [hM])
    (by rw [hM]; omega) run
  obtain ⟨hown, G3, run⟩ := ric_ownerGuard hfork rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_iszero s1
  obtain ⟨hdl, G7, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_timestamp s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_iszero s1
  obtain ⟨hnof, G28, run⟩ := ric_assertJump rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_swap rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G35, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G43, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G44, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G45, rfl⟩ := ri_sstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G46, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G47, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G48, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G49, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G50, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G51, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G52, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G53, rfl⟩ := ri_log3 s1
  cases run with
  | last hl =>
  cases hl
  clear * - hc hdec hv hown hcl hdl hnof hfork
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  generalize vyMem Mem.empty (Sevm.dataWord sevm 0) = M0 at hwf0 ⊢
  have ha0 : Sevm.dataWord sevm (Bytes.toB256 [4]) = Sevm.argWord sevm 0 := rfl
  simp only [show (Bytes.toB256 [1, 64]).toNat = 320 from by decide,
    show (Bytes.toB256 [0]).toNat = 0 from by decide,
    show Bytes.toB256 [11] = transferOwnershipDeadlineSlot from by decide,
    show Bytes.toB256 [14] = futureOwnerSlot from by decide, ha0] at hcl hdl hnof ⊢
  generalize hdw : sevm.benvStat.time + Bytes.toB256 [3, 244, 128] = d
  mem_reads
  simp only [getStorVal_afterSload, getStorVal_eq_getStor, afterSload_getStor] at hdl
  have hdlN : s.transferOwnershipDeadline = 0 := by
    rw [← hc.abs.transferOwnershipDeadline, eq_zero_of_iszero_ne_zero hdl]; rfl
  have hdN : d.toNat = (quietEnv sevm).time + adminActionsDelay ∧
      (quietEnv sevm).time + adminActionsDelay < wordSize := by
    have hlt := eq_zero_of_iszero_ne_zero hnof
    have hnlt : ¬ (sevm.benvStat.time + Bytes.toB256 [3, 244, 128] < sevm.benvStat.time) := by
      unfold B256.ltCheck at hlt; split at hlt
      · cases hlt
      · assumption
    have hN := (B256.nof_iff_not_add_lt _ _).mpr hnlt
    have c2 : (Bytes.toB256 [3, 244, 128]).toNat = adminActionsDelay := by decide
    rw [c2] at hN
    refine ⟨?_, hN⟩
    rw [← hdw, B256.toNat_add_eq_of_nof _ _ (by rw [B256.Nof, c2]; exact hN), c2]; rfl
  refine ⟨⟨{ s with transferOwnershipDeadline := d.toNat, futureOwner := arg sevm 0 }, none,
    [.commitNewAdmin d.toNat (arg sevm 0)], []⟩, ?_, ?_⟩
  · rw [hdec]
    simp only [step, body, Curve3Pool.commitTransferOwnership, quietEnv_value hv,
      quietEnv_owner hc hown, hdlN, chkAdd, hdN.2, req, ite_true]
    simp only [arg, hcl, ite_true]
    rw [← hdN.1]; rfl
  refine quietLands_stopLog ((((((QStep.refl sevm b).sload ownerSlot).sload
    transferOwnershipDeadlineSlot).sstore transferOwnershipDeadlineSlot d).sstore futureOwnerSlot
    (Sevm.argWord sevm 0))) ⟨fun x hx => ?_, fun f hf => ?_⟩ ?_ rfl rfl
  · rw [hdec] at hx
    simp only [footprint, List.mem_cons, forall_eq_or_imp, Fld.slot] at hx
    obtain ⟨h1, h2, -⟩ := hx
    rw [Stor.get_set_ne _ h2, Stor.get_set_ne _ h1]
  · rw [hdec] at hf
    simp only [footprint, List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl <;>
      simp (disch := decide) only [Fld.Reads, Stor.get_set_ne, Stor.get_set_self] <;> rfl
  · simp only [List.map_cons, List.map_nil, eventLog, arg, Jaune.toB256_toNat]
    rfl

end

end Blanc.Lift.Curve3Pool
