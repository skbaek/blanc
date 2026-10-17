import Blanc.Composition.UniswapV2PairWeth9CapstoneFeeToHash
import Blanc.Lift.UniswapV2Pair.PairTraceKeys

/-!
# Every precompile's answer to `feeTo()` under BPO2

`feeTo_precompileRows`: the rows the precompiles' successful answers to the 4-byte `feeTo()` request
select (`mintFeeReplyKeys`'s precompile half): `ECRECOVER` and `P256VERIFY` answer the empty string,
`SHA256`, `RIPEMD160` and the identity answer their digests and the request itself; every other
precompile fails on this request at any gas (an input-length check, an invalid curve point, a
`MODEXP` length beyond EIP-7823's bound).
-/

namespace Blanc.Composition.UniswapV2PairWeth9Capstone

open Jaune Blanc Blanc.Lift Blanc.Lift.UniswapV2Pair

theorem answer_some {data : Bytes} {rules : ModexpRules} {adr : Adr} {e : Evm} {c : Nat} {o : Bytes}
    (hd : e.sta.data = data) (hr : e.sta.benvStat.rules.modexp = rules)
    (h : precompileRun e adr = .ok c o) : precompileAnswer data rules adr = some o := by
  rw [← hd, ← hr]
  exact precompileAnswer_of_ok h

theorem answer_none {data : Bytes} {rules : ModexpRules} {adr : Adr}
    (h : ∀ e : Evm, e.sta.data = data → e.sta.benvStat.rules.modexp = rules →
      ∀ c o, precompileRun e adr ≠ .ok c o) : precompileAnswer data rules adr = none := by
  unfold precompileAnswer
  rw [dite_eq_right]
  rintro ⟨o, e, c, hd, hr, hrun⟩
  exact h e hd hr c o hrun

/-- A BPO2 machine carrying `feeTo()` with ample gas. -/
def feeToEvm : Evm := initEvm
  { (default : Msg) with
    data := feeToData, gas := 1000000,
    benv := { (default : Benv) with stat := { (default : BenvStat) with fork := .bpo2 } } }

/-- A precompile whose input-length check rejects `feeTo()` never answers it. -/
macro "precheck_fail " h:ident : tactic =>
  `(tactic| (dsimp only at $h:ident; split at $h:ident <;>
    first | cases $h:ident | (exfalso; rename_i hc _; revert hc; decide)))

local notation "M" => Fork.bpo2.ruleSet.modexp

theorem answer_9 : precompileAnswer feeToData M 9 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 9 = executeBlake2F e from rfl] at h
    unfold executeBlake2F at h; rw [hd] at h; precheck_fail h

theorem answer_10 : precompileAnswer feeToData M 10 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 10 = executePointEval e from rfl] at h
    unfold executePointEval at h; rw [hd] at h; precheck_fail h

theorem answer_11 : precompileAnswer feeToData M 11 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 11 = executeBls12G1Add e from rfl] at h
    unfold executeBls12G1Add at h; rw [hd] at h; precheck_fail h

theorem answer_12 : precompileAnswer feeToData M 12 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 12 = executeBls12G1Msm e from rfl] at h
    unfold executeBls12G1Msm at h; rw [hd] at h; precheck_fail h

theorem answer_13 : precompileAnswer feeToData M 13 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 13 = executeBls12G2Add e from rfl] at h
    unfold executeBls12G2Add at h; rw [hd] at h; precheck_fail h

theorem answer_14 : precompileAnswer feeToData M 14 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 14 = executeBls12G2Msm e from rfl] at h
    unfold executeBls12G2Msm at h; rw [hd] at h; precheck_fail h

theorem answer_15 : precompileAnswer feeToData M 15 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 15 = executeBls12Pairing e from rfl] at h
    unfold executeBls12Pairing at h; rw [hd] at h; precheck_fail h

theorem answer_16 : precompileAnswer feeToData M 16 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 16 = executeBls12MapFpToG1 e from rfl] at h
    unfold executeBls12MapFpToG1 at h; rw [hd] at h; precheck_fail h

theorem answer_17 : precompileAnswer feeToData M 17 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 17 = executeBls12MapFp2ToG2 e from rfl] at h
    unfold executeBls12MapFp2ToG2 at h; rw [hd] at h; precheck_fail h

theorem answer_8 : precompileAnswer feeToData M 8 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 8 = executePairingCheck e from rfl] at h
    unfold executePairingCheck PrecompResult.chargeGas at h; rw [hd] at h; dsimp only at h
    split at h
    · rw [show executePairingCheckInner feeToData (34000 * (feeToData.length / 192) + 45000) =
        .error ⟨.halt (.outOfGas .none), 34000 * (feeToData.length / 192) + 45000⟩ from rfl] at h
      cases h
    · cases h

theorem answer_6 : precompileAnswer feeToData M 6 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 6 = executeEcadd e from rfl] at h
    unfold executeEcadd PrecompResult.chargeGas at h; rw [hd] at h; dsimp only at h
    split at h
    · split at h
      · cases h
      · rw [show BNP.mk? (Bytes.toNat (List.sliceD feeToData 0 32 0))
            (Bytes.toNat (List.sliceD feeToData 32 32 0)) = none by decide +kernel] at h
        cases h
    · cases h

theorem answer_7 : precompileAnswer feeToData M 7 = none :=
  answer_none fun e hd _ c o h => by
    rw [show precompileRun e 7 = executeEcmul e from rfl] at h
    unfold executeEcmul PrecompResult.chargeGas at h; rw [hd] at h; dsimp only at h
    split at h
    · split at h
      · cases h
      · rw [show BNP.mk? (Bytes.toNat (List.sliceD feeToData 0 32 0))
            (Bytes.toNat (List.sliceD feeToData 32 32 0)) = none by decide +kernel] at h
        cases h
    · cases h

theorem answer_5 : precompileAnswer feeToData M 5 = none :=
  answer_none fun e hd hr c o h => by
    rw [show precompileRun e 5 = executeModexp e from rfl] at h
    unfold executeModexp at h; rw [hd, hr] at h; dsimp only at h
    split at h
    · cases h
    · rename_i hc; exfalso; revert hc; decide +kernel

theorem answer_1 : precompileAnswer feeToData M 1 = some [] :=
  answer_some (e := feeToEvm) (c := gasEcrecover) rfl rfl rfl

theorem answer_2 : precompileAnswer feeToData M 2 = some (Bytes.sha256 feeToData).toBytes :=
  answer_some (e := feeToEvm) (c := 72) rfl rfl rfl

theorem answer_3 : precompileAnswer feeToData M 3 =
    some (B256.toBytes (Bytes.toB256 (Bytes.ripemd160 feeToData))) :=
  answer_some (e := feeToEvm) (c := 720) rfl rfl rfl

theorem answer_4 : precompileAnswer feeToData M 4 = some feeToData :=
  answer_some (e := feeToEvm) (c := 18) rfl rfl rfl

theorem answer_256 : precompileAnswer feeToData M 256 = some [] :=
  answer_some (e := feeToEvm) (c := gasP256Verify) rfl rfl rfl

/-- The rows the precompiles' answers to `feeTo()` select. -/
def feeToRows : List WriterKey :=
  [mintReplyRow [], mintReplyRow (Bytes.sha256 feeToData).toBytes,
    mintReplyRow (B256.toBytes (Bytes.toB256 (Bytes.ripemd160 feeToData))), mintReplyRow feeToData,
    mintReplyRow []]

/-- **The precompile half of a BPO2 Pair frame's reply rows.** -/
theorem feeTo_precompileRows :
    precompileRunAddresses.filterMap (fun adr =>
      (precompileAnswer (ExternalOperation.encode .feeTo) M adr).map mintReplyRow) = feeToRows := by
  change precompileRunAddresses.filterMap (fun adr =>
      (precompileAnswer feeToData M adr).map mintReplyRow) = feeToRows
  simp only [precompileRunAddresses, List.filterMap_cons, List.filterMap_nil, answer_1, answer_2,
    answer_3, answer_4, answer_5, answer_6, answer_7, answer_8, answer_9, answer_10, answer_11,
    answer_12, answer_13, answer_14, answer_15, answer_16, answer_17, answer_256, Option.map_some,
    Option.map_none]
  rfl

end Blanc.Composition.UniswapV2PairWeth9Capstone
