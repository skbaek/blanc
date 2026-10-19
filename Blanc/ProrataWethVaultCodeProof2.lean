-- GENERATED FILE: scripts/gen-prorata-weth-vault-code.lean
-- Maintained proof text: scripts/prorata-weth-vault-code-proof2.lean.in
import Blanc.ProrataWethVaultCodeProof1
import Blanc.CompiledShape

namespace Blanc
open Jaune CompiledShape
open scoped CompiledShape
namespace ProrataWethVaultCodeProof

open ProrataWethVault in
private def depositViewArithmetic : Func :=
  Func.branch (mulDiv (arg 0) stagedDenominator stagedAssetFactor .down returnWordSlot)
    (productOverTwoPow256 (arg 0) stagedDenominator .down returnWordSlot)
private def depositViewAssets : Func := previewRedeemAssetsPrefix +++ depositViewArithmetic
private def depositViewStage : Func := previewRedeemStagePrefix +++ Func.branch depositViewAssets Func.revert
private def depositViewReturnSize : Func := maxDepositReturnSizePrefix +++ Func.branch depositViewStage Func.revert
private def depositViewRead : Func := maxDepositReadPrefix +++ Func.branch depositViewReturnSize Func.revert
private def depositViewStatic : Func := maxDepositStaticPrefix +++ Func.branch depositViewRead Func.revert
open ProrataWethVault in
private theorem depositViewMul_source_cut :
    mulDiv (arg 0) stagedDenominator stagedAssetFactor .down returnWordSlot =
      previewWithdrawMulStage +++ maxDepositMulRecover +++ divide512 .down returnWordSlot := by rfl
open ProrataWethVault in
private theorem depositViewProduct_source_cut :
    productOverTwoPow256 (arg 0) stagedDenominator .down returnWordSlot =
      previewWithdrawMultiplyStage +++ maxDepositMulRecover +++ depositProductTail +++
        finishQuotient .down returnWordSlot := by rfl

private theorem depositViewWideCore_348_compile :
    Func.compile vaultTable 348
      (ProrataWethVault.divideWideCore .down ProrataWethVault.returnWordSlot) =
      some (prorataWethVaultCodeChunk1.drop 92 ++ prorataWethVaultCodeChunk2.take 191) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk1.drop 92).take 117 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk1.drop 209 ++ prorataWethVaultCodeChunk2.take 44 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk2.drop 44).take 126 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk2.drop 44).take 63 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk2.drop 107).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : ((prorataWethVaultCodeChunk2.drop 44).take 63) ++ ((prorataWethVaultCodeChunk2.drop 107).take 63) = (prorataWethVaultCodeChunk2.drop 44).take 126 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk2.drop 44) (i := 63) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk2.drop 170).take 13 := by rfl
  have hfinish : ([0x61, 0x03, 0x00, 0x51, 0x61, 0x3d, 0x33, 0x56] : Bytes) = (prorataWethVaultCodeChunk2.drop 183).take 8 := by rfl
  rw [divideWideCore_down_compile_at, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs, hfinish]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk1.drop 92).take 117) ++ (prorataWethVaultCodeChunk1.drop 209) = prorataWethVaultCodeChunk1.drop 92 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 117 (prorataWethVaultCodeChunk1.drop 92)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 92).take 117), hj0]
  have hj1 : (prorataWethVaultCodeChunk2.take 44) ++ ((prorataWethVaultCodeChunk2.drop 44).take 126) = prorataWethVaultCodeChunk2.take 170 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 44) (j := 126)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk2.take 44), hj1]
  have hj2 : (prorataWethVaultCodeChunk2.take 170) ++ ((prorataWethVaultCodeChunk2.drop 170).take 13) = prorataWethVaultCodeChunk2.take 183 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 170) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk2.take 170), hj2]
  have hj3 : (prorataWethVaultCodeChunk2.take 183) ++ ((prorataWethVaultCodeChunk2.drop 183).take 8) = prorataWethVaultCodeChunk2.take 191 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 183) (j := 8)).symm
  rw [hj3]

private theorem depositViewSimple_704_compile :
    Func.compile vaultTable 704 (ProrataWethVault.divideSimple .down ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk2.drop 192).take 34) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem depositViewWide_331_compile :
    Func.compile vaultTable 331 (ProrataWethVault.divideWide .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk1.drop 75 ++ prorataWethVaultCodeChunk2.take 191) := by
  rw [divideWide_down_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk1.drop 75).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 340 347 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk1.drop 92 ++ prorataWethVaultCodeChunk2.take 191)
    (revert_compile_at 344) (by rw [hlen]) (by decide) depositViewWideCore_348_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (347 >>> 8).toUInt8, Nat.toUInt8 347, 0x57] : Bytes) = (prorataWethVaultCodeChunk1.drop 84).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk1.drop 91).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk1.drop 88).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk1.drop 75).take 9) ++ ((prorataWethVaultCodeChunk1.drop 84).take 4) = (prorataWethVaultCodeChunk1.drop 75).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk1.drop 75) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 75).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk1.drop 75).take 13) ++ ((prorataWethVaultCodeChunk1.drop 88).take 3) = (prorataWethVaultCodeChunk1.drop 75).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk1.drop 75) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 75).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk1.drop 75).take 16) ++ ((prorataWethVaultCodeChunk1.drop 91).take 1) = (prorataWethVaultCodeChunk1.drop 75).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk1.drop 75) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 75).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk1.drop 75).take 17) ++ (prorataWethVaultCodeChunk1.drop 92) = prorataWethVaultCodeChunk1.drop 75 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk1.drop 75)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 75).take 17), hj3]

private theorem depositViewNonzero_322_compile :
    Func.compile vaultTable 322 (divide512NonzeroDown) = some (prorataWethVaultCodeChunk1.drop 66 ++ prorataWethVaultCodeChunk2.take 226) := by
  rw [divide512NonzeroDown, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk1.drop 66).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk1.drop 75 ++ prorataWethVaultCodeChunk2.take 191) : Bytes).length = 372 := by decide +kernel
  have hbranch := compile_branch vaultTable 327 703 _ _
    (prorataWethVaultCodeChunk1.drop 75 ++ prorataWethVaultCodeChunk2.take 191) ((prorataWethVaultCodeChunk2.drop 192).take 34)
    depositViewWide_331_compile (by rw [hlen]) (by decide) depositViewSimple_704_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (703 >>> 8).toUInt8, Nat.toUInt8 703, 0x57] : Bytes) = (prorataWethVaultCodeChunk1.drop 71).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk2.drop 191).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk1.drop 66).take 5) ++ ((prorataWethVaultCodeChunk1.drop 71).take 4) = (prorataWethVaultCodeChunk1.drop 66).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk1.drop 66) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 66).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk1.drop 66).take 9) ++ (prorataWethVaultCodeChunk1.drop 75) = prorataWethVaultCodeChunk1.drop 66 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk1.drop 66)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 66).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk2.take 191) ++ ((prorataWethVaultCodeChunk2.drop 191).take 1) = prorataWethVaultCodeChunk2.take 192 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 191) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk2.take 191), hj2]
  have hj3 : (prorataWethVaultCodeChunk2.take 192) ++ ((prorataWethVaultCodeChunk2.drop 192).take 34) = prorataWethVaultCodeChunk2.take 226 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 192) (j := 34)).symm
  rw [hj3]

private theorem depositViewDivide_313_compile :
    Func.compile vaultTable 313 (ProrataWethVault.divide512 .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk1.drop 57 ++ prorataWethVaultCodeChunk2.take 230) := by
  rw [divide512_down_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk1.drop 57).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk1.drop 66 ++ prorataWethVaultCodeChunk2.take 226) : Bytes).length = 416 := by decide +kernel
  have hbranch := compile_branch vaultTable 318 738 _ _
    (prorataWethVaultCodeChunk1.drop 66 ++ prorataWethVaultCodeChunk2.take 226) [0x5f, 0x5f, 0xfd]
    depositViewNonzero_322_compile (by rw [hlen]) (by decide) (revert_compile_at 739)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (738 >>> 8).toUInt8, Nat.toUInt8 738, 0x57] : Bytes) = (prorataWethVaultCodeChunk1.drop 62).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk2.drop 226).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk2.drop 227).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk1.drop 57).take 5) ++ ((prorataWethVaultCodeChunk1.drop 62).take 4) = (prorataWethVaultCodeChunk1.drop 57).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk1.drop 57) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 57).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk1.drop 57).take 9) ++ (prorataWethVaultCodeChunk1.drop 66) = prorataWethVaultCodeChunk1.drop 57 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk1.drop 57)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk1.drop 57).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk2.take 226) ++ ((prorataWethVaultCodeChunk2.drop 226).take 1) = prorataWethVaultCodeChunk2.take 227 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 226) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk2.take 226), hj2]
  have hj3 : (prorataWethVaultCodeChunk2.take 227) ++ ((prorataWethVaultCodeChunk2.drop 227).take 3) = prorataWethVaultCodeChunk2.take 230 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 227) (j := 3)).symm
  rw [hj3]

private theorem depositViewFinish_876_compile :
    Func.compile vaultTable 876 (ProrataWethVault.finishQuotient .down ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk3.drop 108).take 8) := by
  rw [finishQuotient_down_compile_at]
  rfl

private theorem depositViewMul_185_compile :
    Func.compile vaultTable 185 (ProrataWethVault.mulDiv (arg 0) ProrataWethVault.stagedDenominator ProrataWethVault.stagedAssetFactor .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk0.drop 185 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2.take 230) := by
  have hb0 : previewWithdrawMulStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk0.drop 185).take 43 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = prorataWethVaultCodeChunk0.drop 228 ++ prorataWethVaultCodeChunk1.take 57 := by
    rfl
  rw [depositViewMul_source_cut]
  rw [compile_prepend, previewWithdrawMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [depositViewDivide_313_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 185).take 43) ++ (prorataWethVaultCodeChunk0.drop 228) = prorataWethVaultCodeChunk0.drop 185 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 43 (prorataWethVaultCodeChunk0.drop 185)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 185).take 43), hj0]
  have hj1 : (prorataWethVaultCodeChunk1.take 57) ++ (prorataWethVaultCodeChunk1.drop 57) = prorataWethVaultCodeChunk1 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 57 (prorataWethVaultCodeChunk1)
  rw [← List.append_assoc (prorataWethVaultCodeChunk1.take 57), hj1]

private theorem depositViewProduct_743_compile :
    Func.compile vaultTable 743 (ProrataWethVault.productOverTwoPow256 (arg 0) ProrataWethVault.stagedDenominator .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk2.drop 231 ++ prorataWethVaultCodeChunk3.take 116) := by
  have hb0 : previewWithdrawMultiplyStage.flatMap Ninst.toBytes = prorataWethVaultCodeChunk2.drop 231 ++ prorataWethVaultCodeChunk3.take 7 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk3.drop 7).take 85 := by
    rfl
  have hb2 : depositProductTail.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk3.drop 92).take 16 := by
    rfl
  rw [depositViewProduct_source_cut]
  rw [compile_prepend, previewWithdrawMultiplyStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, depositProductTail_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [depositViewFinish_876_compile, hb0, hb1, hb2]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk3.take 7) ++ ((prorataWethVaultCodeChunk3.drop 7).take 85) = prorataWethVaultCodeChunk3.take 92 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 7) (j := 85)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 7), hj0]
  have hj1 : (prorataWethVaultCodeChunk3.take 92) ++ ((prorataWethVaultCodeChunk3.drop 92).take 16) = prorataWethVaultCodeChunk3.take 108 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 92) (j := 16)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 92), hj1]
  have hj2 : (prorataWethVaultCodeChunk3.take 108) ++ ((prorataWethVaultCodeChunk3.drop 108).take 8) = prorataWethVaultCodeChunk3.take 116 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 108) (j := 8)).symm
  rw [hj2]

private theorem depositViewArithmetic_181_compile :
    Func.compile vaultTable 181 (depositViewArithmetic) = some (prorataWethVaultCodeChunk0.drop 181 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 116) := by
  rw [depositViewArithmetic]
  have hlen : ((prorataWethVaultCodeChunk0.drop 185 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2.take 230) : Bytes).length = 557 := by decide +kernel
  have hbranch := compile_branch vaultTable 181 742 _ _
    (prorataWethVaultCodeChunk0.drop 185 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2.take 230) (prorataWethVaultCodeChunk2.drop 231 ++ prorataWethVaultCodeChunk3.take 116)
    depositViewMul_185_compile (by rw [hlen]) (by decide) depositViewProduct_743_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (742 >>> 8).toUInt8, Nat.toUInt8 742, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 181).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk2.drop 230).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 181).take 4) ++ (prorataWethVaultCodeChunk0.drop 185) = prorataWethVaultCodeChunk0.drop 181 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk0.drop 181)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 181).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk2.take 230) ++ ((prorataWethVaultCodeChunk2.drop 230).take 1) = prorataWethVaultCodeChunk2.take 231 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk2) (i := 230) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk2.take 230), hj1]
  have hj2 : (prorataWethVaultCodeChunk2.take 231) ++ (prorataWethVaultCodeChunk2.drop 231) = prorataWethVaultCodeChunk2 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 231 (prorataWethVaultCodeChunk2)
  rw [← List.append_assoc (prorataWethVaultCodeChunk2.take 231), hj2]

private theorem depositViewAssets_175_compile :
    Func.compile vaultTable 175 (depositViewAssets) = some (prorataWethVaultCodeChunk0.drop 175 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 116) := by
  have hb0 : previewRedeemAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk0.drop 175).take 6 := by
    rw [previewRedeemAssetsPrefix_bytes]
    rfl
  rw [depositViewAssets]
  rw [compile_prepend, previewRedeemAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [depositViewArithmetic_181_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 175).take 6) ++ (prorataWethVaultCodeChunk0.drop 181) = prorataWethVaultCodeChunk0.drop 175 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 6 (prorataWethVaultCodeChunk0.drop 175)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 175).take 6), hj0]

private theorem depositViewStage_120_compile :
    Func.compile vaultTable 120 (depositViewStage) = some (prorataWethVaultCodeChunk0.drop 120 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 120) := by
  rw [depositViewStage, compile_prepend, previewRedeemStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : previewRedeemStagePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk0.drop 120).take 51 := by
    rw [previewRedeemStagePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk0.drop 175 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 116) : Bytes).length = 709 := by decide +kernel
  have hbranch := compile_branch vaultTable 171 884 _ _
    (prorataWethVaultCodeChunk0.drop 175 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 116) [0x5f, 0x5f, 0xfd]
    depositViewAssets_175_compile (by rw [hlen]) (by decide) (revert_compile_at 885)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (884 >>> 8).toUInt8, Nat.toUInt8 884, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 171).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 116).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk3.drop 117).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 120).take 51) ++ ((prorataWethVaultCodeChunk0.drop 171).take 4) = (prorataWethVaultCodeChunk0.drop 120).take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk0.drop 120) (i := 51) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 120).take 51), hj0]
  have hj1 : ((prorataWethVaultCodeChunk0.drop 120).take 55) ++ (prorataWethVaultCodeChunk0.drop 175) = prorataWethVaultCodeChunk0.drop 120 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 55 (prorataWethVaultCodeChunk0.drop 120)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 120).take 55), hj1]
  have hj2 : (prorataWethVaultCodeChunk3.take 116) ++ ((prorataWethVaultCodeChunk3.drop 116).take 1) = prorataWethVaultCodeChunk3.take 117 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 116) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 116), hj2]
  have hj3 : (prorataWethVaultCodeChunk3.take 117) ++ ((prorataWethVaultCodeChunk3.drop 117).take 3) = prorataWethVaultCodeChunk3.take 120 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 117) (j := 3)).symm
  rw [hj3]

private theorem depositViewReturnSize_111_compile :
    Func.compile vaultTable 111 (depositViewReturnSize) = some (prorataWethVaultCodeChunk0.drop 111 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 124) := by
  rw [depositViewReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk0.drop 111).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk0.drop 120 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 120) : Bytes).length = 768 := by decide +kernel
  have hbranch := compile_branch vaultTable 116 888 _ _
    (prorataWethVaultCodeChunk0.drop 120 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 120) [0x5f, 0x5f, 0xfd]
    depositViewStage_120_compile (by rw [hlen]) (by decide) (revert_compile_at 889)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (888 >>> 8).toUInt8, Nat.toUInt8 888, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 116).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 120).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk3.drop 121).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 111).take 5) ++ ((prorataWethVaultCodeChunk0.drop 116).take 4) = (prorataWethVaultCodeChunk0.drop 111).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk0.drop 111) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 111).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk0.drop 111).take 9) ++ (prorataWethVaultCodeChunk0.drop 120) = prorataWethVaultCodeChunk0.drop 111 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk0.drop 111)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 111).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk3.take 120) ++ ((prorataWethVaultCodeChunk3.drop 120).take 1) = prorataWethVaultCodeChunk3.take 121 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 120) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 120), hj2]
  have hj3 : (prorataWethVaultCodeChunk3.take 121) ++ ((prorataWethVaultCodeChunk3.drop 121).take 3) = prorataWethVaultCodeChunk3.take 124 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 121) (j := 3)).symm
  rw [hj3]

private theorem depositViewRead_83_compile :
    Func.compile vaultTable 83 (depositViewRead) = some (prorataWethVaultCodeChunk0.drop 83 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 128) := by
  rw [depositViewRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk0.drop 83).take 24 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk0.drop 111 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 124) : Bytes).length = 781 := by decide +kernel
  have hbranch := compile_branch vaultTable 107 892 _ _
    (prorataWethVaultCodeChunk0.drop 111 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 124) [0x5f, 0x5f, 0xfd]
    depositViewReturnSize_111_compile (by rw [hlen]) (by decide) (revert_compile_at 893)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (892 >>> 8).toUInt8, Nat.toUInt8 892, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 107).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 124).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk3.drop 125).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 83).take 24) ++ ((prorataWethVaultCodeChunk0.drop 107).take 4) = (prorataWethVaultCodeChunk0.drop 83).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk0.drop 83) (i := 24) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 83).take 24), hj0]
  have hj1 : ((prorataWethVaultCodeChunk0.drop 83).take 28) ++ (prorataWethVaultCodeChunk0.drop 111) = prorataWethVaultCodeChunk0.drop 83 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 28 (prorataWethVaultCodeChunk0.drop 83)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 83).take 28), hj1]
  have hj2 : (prorataWethVaultCodeChunk3.take 124) ++ ((prorataWethVaultCodeChunk3.drop 124).take 1) = prorataWethVaultCodeChunk3.take 125 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 124) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 124), hj2]
  have hj3 : (prorataWethVaultCodeChunk3.take 125) ++ ((prorataWethVaultCodeChunk3.drop 125).take 3) = prorataWethVaultCodeChunk3.take 128 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 125) (j := 3)).symm
  rw [hj3]

private theorem depositViewStatic_75_compile :
    Func.compile vaultTable 75 (depositViewStatic) = some (prorataWethVaultCodeChunk0.drop 75 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 132) := by
  rw [depositViewStatic, compile_prepend, maxDepositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk0.drop 75).take 4 := by
    rw [maxDepositStaticPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk0.drop 83 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 128) : Bytes).length = 813 := by decide +kernel
  have hbranch := compile_branch vaultTable 79 896 _ _
    (prorataWethVaultCodeChunk0.drop 83 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 128) [0x5f, 0x5f, 0xfd]
    depositViewRead_83_compile (by rw [hlen]) (by decide) (revert_compile_at 897)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (896 >>> 8).toUInt8, Nat.toUInt8 896, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 79).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 128).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk3.drop 129).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 75).take 4) ++ ((prorataWethVaultCodeChunk0.drop 79).take 4) = (prorataWethVaultCodeChunk0.drop 75).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk0.drop 75) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 75).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk0.drop 75).take 8) ++ (prorataWethVaultCodeChunk0.drop 83) = prorataWethVaultCodeChunk0.drop 75 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk0.drop 75)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 75).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk3.take 128) ++ ((prorataWethVaultCodeChunk3.drop 128).take 1) = prorataWethVaultCodeChunk3.take 129 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 128) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 128), hj2]
  have hj3 : (prorataWethVaultCodeChunk3.take 129) ++ ((prorataWethVaultCodeChunk3.drop 129).take 3) = prorataWethVaultCodeChunk3.take 132 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 129) (j := 3)).symm
  rw [hj3]

private theorem previewDeposit_source_cut : ProrataWethVault.routed 1 ProrataWethVault.previewDeposit = nonpayable depositViewStatic := by rfl
private theorem previewDeposit_endpoint_compile :
    Func.compile vaultTable 65 (ProrataWethVault.routed 1 ProrataWethVault.previewDeposit) = some (prorataWethVaultCodeChunk0.drop 65 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 132) := by
  rw [previewDeposit_source_cut]
  have hcut : nonpayable depositViewStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert depositViewStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 67 74 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk0.drop 75 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 132)
    (revert_compile_at 71) (by rfl) (by decide) depositViewStatic_75_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (74 >>> 8).toUInt8, Nat.toUInt8 74, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk0.drop 65).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (74 >>> 8).toUInt8, Nat.toUInt8 74, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 65).take 10) ++ (prorataWethVaultCodeChunk0.drop 75) = prorataWethVaultCodeChunk0.drop 65 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk0.drop 65)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 65).take 10), hj0]

private theorem depositViewWideCore_2673_compile :
    Func.compile vaultTable 2673
      (ProrataWethVault.divideWideCore .down ProrataWethVault.returnWordSlot) =
      some (prorataWethVaultCodeChunk10.drop 113 ++ prorataWethVaultCodeChunk11.take 212) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk10.drop 113).take 117 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk10.drop 230 ++ prorataWethVaultCodeChunk11.take 65 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk11.drop 65).take 126 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk11.drop 65).take 63 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk11.drop 128).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : ((prorataWethVaultCodeChunk11.drop 65).take 63) ++ ((prorataWethVaultCodeChunk11.drop 128).take 63) = (prorataWethVaultCodeChunk11.drop 65).take 126 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk11.drop 65) (i := 63) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk11.drop 191).take 13 := by rfl
  have hfinish : ([0x61, 0x03, 0x00, 0x51, 0x61, 0x3d, 0x33, 0x56] : Bytes) = (prorataWethVaultCodeChunk11.drop 204).take 8 := by rfl
  rw [divideWideCore_down_compile_at, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs, hfinish]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk10.drop 113).take 117) ++ (prorataWethVaultCodeChunk10.drop 230) = prorataWethVaultCodeChunk10.drop 113 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 117 (prorataWethVaultCodeChunk10.drop 113)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 113).take 117), hj0]
  have hj1 : (prorataWethVaultCodeChunk11.take 65) ++ ((prorataWethVaultCodeChunk11.drop 65).take 126) = prorataWethVaultCodeChunk11.take 191 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 65) (j := 126)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk11.take 65), hj1]
  have hj2 : (prorataWethVaultCodeChunk11.take 191) ++ ((prorataWethVaultCodeChunk11.drop 191).take 13) = prorataWethVaultCodeChunk11.take 204 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 191) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk11.take 191), hj2]
  have hj3 : (prorataWethVaultCodeChunk11.take 204) ++ ((prorataWethVaultCodeChunk11.drop 204).take 8) = prorataWethVaultCodeChunk11.take 212 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 204) (j := 8)).symm
  rw [hj3]

private theorem depositViewSimple_3029_compile :
    Func.compile vaultTable 3029 (ProrataWethVault.divideSimple .down ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk11.drop 213).take 34) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem depositViewWide_2656_compile :
    Func.compile vaultTable 2656 (ProrataWethVault.divideWide .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk10.drop 96 ++ prorataWethVaultCodeChunk11.take 212) := by
  rw [divideWide_down_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk10.drop 96).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 2665 2672 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk10.drop 113 ++ prorataWethVaultCodeChunk11.take 212)
    (revert_compile_at 2669) (by rw [hlen]) (by decide) depositViewWideCore_2673_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2672 >>> 8).toUInt8, Nat.toUInt8 2672, 0x57] : Bytes) = (prorataWethVaultCodeChunk10.drop 105).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk10.drop 112).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk10.drop 109).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk10.drop 96).take 9) ++ ((prorataWethVaultCodeChunk10.drop 105).take 4) = (prorataWethVaultCodeChunk10.drop 96).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk10.drop 96) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 96).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk10.drop 96).take 13) ++ ((prorataWethVaultCodeChunk10.drop 109).take 3) = (prorataWethVaultCodeChunk10.drop 96).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk10.drop 96) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 96).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk10.drop 96).take 16) ++ ((prorataWethVaultCodeChunk10.drop 112).take 1) = (prorataWethVaultCodeChunk10.drop 96).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk10.drop 96) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 96).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk10.drop 96).take 17) ++ (prorataWethVaultCodeChunk10.drop 113) = prorataWethVaultCodeChunk10.drop 96 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk10.drop 96)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 96).take 17), hj3]

private theorem depositViewNonzero_2647_compile :
    Func.compile vaultTable 2647 (divide512NonzeroDown) = some (prorataWethVaultCodeChunk10.drop 87 ++ prorataWethVaultCodeChunk11.take 247) := by
  rw [divide512NonzeroDown, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk10.drop 87).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk10.drop 96 ++ prorataWethVaultCodeChunk11.take 212) : Bytes).length = 372 := by decide +kernel
  have hbranch := compile_branch vaultTable 2652 3028 _ _
    (prorataWethVaultCodeChunk10.drop 96 ++ prorataWethVaultCodeChunk11.take 212) ((prorataWethVaultCodeChunk11.drop 213).take 34)
    depositViewWide_2656_compile (by rw [hlen]) (by decide) depositViewSimple_3029_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3028 >>> 8).toUInt8, Nat.toUInt8 3028, 0x57] : Bytes) = (prorataWethVaultCodeChunk10.drop 92).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk11.drop 212).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk10.drop 87).take 5) ++ ((prorataWethVaultCodeChunk10.drop 92).take 4) = (prorataWethVaultCodeChunk10.drop 87).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk10.drop 87) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 87).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk10.drop 87).take 9) ++ (prorataWethVaultCodeChunk10.drop 96) = prorataWethVaultCodeChunk10.drop 87 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk10.drop 87)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 87).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk11.take 212) ++ ((prorataWethVaultCodeChunk11.drop 212).take 1) = prorataWethVaultCodeChunk11.take 213 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 212) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk11.take 212), hj2]
  have hj3 : (prorataWethVaultCodeChunk11.take 213) ++ ((prorataWethVaultCodeChunk11.drop 213).take 34) = prorataWethVaultCodeChunk11.take 247 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 213) (j := 34)).symm
  rw [hj3]

private theorem depositViewDivide_2638_compile :
    Func.compile vaultTable 2638 (ProrataWethVault.divide512 .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk10.drop 78 ++ prorataWethVaultCodeChunk11.take 251) := by
  rw [divide512_down_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk10.drop 78).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk10.drop 87 ++ prorataWethVaultCodeChunk11.take 247) : Bytes).length = 416 := by decide +kernel
  have hbranch := compile_branch vaultTable 2643 3063 _ _
    (prorataWethVaultCodeChunk10.drop 87 ++ prorataWethVaultCodeChunk11.take 247) [0x5f, 0x5f, 0xfd]
    depositViewNonzero_2647_compile (by rw [hlen]) (by decide) (revert_compile_at 3064)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3063 >>> 8).toUInt8, Nat.toUInt8 3063, 0x57] : Bytes) = (prorataWethVaultCodeChunk10.drop 83).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk11.drop 247).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk11.drop 248).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk10.drop 78).take 5) ++ ((prorataWethVaultCodeChunk10.drop 83).take 4) = (prorataWethVaultCodeChunk10.drop 78).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk10.drop 78) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 78).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk10.drop 78).take 9) ++ (prorataWethVaultCodeChunk10.drop 87) = prorataWethVaultCodeChunk10.drop 78 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk10.drop 78)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk10.drop 78).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk11.take 247) ++ ((prorataWethVaultCodeChunk11.drop 247).take 1) = prorataWethVaultCodeChunk11.take 248 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 247) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk11.take 247), hj2]
  have hj3 : (prorataWethVaultCodeChunk11.take 248) ++ ((prorataWethVaultCodeChunk11.drop 248).take 3) = prorataWethVaultCodeChunk11.take 251 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 248) (j := 3)).symm
  rw [hj3]

private theorem depositViewFinish_3201_compile :
    Func.compile vaultTable 3201 (ProrataWethVault.finishQuotient .down ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk12.drop 129).take 8) := by
  rw [finishQuotient_down_compile_at]
  rfl

private theorem depositViewMul_2510_compile :
    Func.compile vaultTable 2510 (ProrataWethVault.mulDiv (arg 0) ProrataWethVault.stagedDenominator ProrataWethVault.stagedAssetFactor .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk9.drop 206 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11.take 251) := by
  have hb0 : previewWithdrawMulStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk9.drop 206).take 43 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = prorataWethVaultCodeChunk9.drop 249 ++ prorataWethVaultCodeChunk10.take 78 := by
    rfl
  rw [depositViewMul_source_cut]
  rw [compile_prepend, previewWithdrawMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [depositViewDivide_2638_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 206).take 43) ++ (prorataWethVaultCodeChunk9.drop 249) = prorataWethVaultCodeChunk9.drop 206 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 43 (prorataWethVaultCodeChunk9.drop 206)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 206).take 43), hj0]
  have hj1 : (prorataWethVaultCodeChunk10.take 78) ++ (prorataWethVaultCodeChunk10.drop 78) = prorataWethVaultCodeChunk10 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 78 (prorataWethVaultCodeChunk10)
  rw [← List.append_assoc (prorataWethVaultCodeChunk10.take 78), hj1]

private theorem depositViewProduct_3068_compile :
    Func.compile vaultTable 3068 (ProrataWethVault.productOverTwoPow256 (arg 0) ProrataWethVault.stagedDenominator .down ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk11.drop 252 ++ prorataWethVaultCodeChunk12.take 137) := by
  have hb0 : previewWithdrawMultiplyStage.flatMap Ninst.toBytes = prorataWethVaultCodeChunk11.drop 252 ++ prorataWethVaultCodeChunk12.take 28 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk12.drop 28).take 85 := by
    rfl
  have hb2 : depositProductTail.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk12.drop 113).take 16 := by
    rfl
  rw [depositViewProduct_source_cut]
  rw [compile_prepend, previewWithdrawMultiplyStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, depositProductTail_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [depositViewFinish_3201_compile, hb0, hb1, hb2]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk12.take 28) ++ ((prorataWethVaultCodeChunk12.drop 28).take 85) = prorataWethVaultCodeChunk12.take 113 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 28) (j := 85)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 28), hj0]
  have hj1 : (prorataWethVaultCodeChunk12.take 113) ++ ((prorataWethVaultCodeChunk12.drop 113).take 16) = prorataWethVaultCodeChunk12.take 129 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 113) (j := 16)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 113), hj1]
  have hj2 : (prorataWethVaultCodeChunk12.take 129) ++ ((prorataWethVaultCodeChunk12.drop 129).take 8) = prorataWethVaultCodeChunk12.take 137 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 129) (j := 8)).symm
  rw [hj2]

private theorem depositViewArithmetic_2506_compile :
    Func.compile vaultTable 2506 (depositViewArithmetic) = some (prorataWethVaultCodeChunk9.drop 202 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 137) := by
  rw [depositViewArithmetic]
  have hlen : ((prorataWethVaultCodeChunk9.drop 206 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11.take 251) : Bytes).length = 557 := by decide +kernel
  have hbranch := compile_branch vaultTable 2506 3067 _ _
    (prorataWethVaultCodeChunk9.drop 206 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11.take 251) (prorataWethVaultCodeChunk11.drop 252 ++ prorataWethVaultCodeChunk12.take 137)
    depositViewMul_2510_compile (by rw [hlen]) (by decide) depositViewProduct_3068_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (3067 >>> 8).toUInt8, Nat.toUInt8 3067, 0x57] : Bytes) = (prorataWethVaultCodeChunk9.drop 202).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk11.drop 251).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 202).take 4) ++ (prorataWethVaultCodeChunk9.drop 206) = prorataWethVaultCodeChunk9.drop 202 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk9.drop 202)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 202).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk11.take 251) ++ ((prorataWethVaultCodeChunk11.drop 251).take 1) = prorataWethVaultCodeChunk11.take 252 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk11) (i := 251) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk11.take 251), hj1]
  have hj2 : (prorataWethVaultCodeChunk11.take 252) ++ (prorataWethVaultCodeChunk11.drop 252) = prorataWethVaultCodeChunk11 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 252 (prorataWethVaultCodeChunk11)
  rw [← List.append_assoc (prorataWethVaultCodeChunk11.take 252), hj2]

private theorem depositViewAssets_2500_compile :
    Func.compile vaultTable 2500 (depositViewAssets) = some (prorataWethVaultCodeChunk9.drop 196 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 137) := by
  have hb0 : previewRedeemAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk9.drop 196).take 6 := by
    rw [previewRedeemAssetsPrefix_bytes]
    rfl
  rw [depositViewAssets]
  rw [compile_prepend, previewRedeemAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [depositViewArithmetic_2506_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 196).take 6) ++ (prorataWethVaultCodeChunk9.drop 202) = prorataWethVaultCodeChunk9.drop 196 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 6 (prorataWethVaultCodeChunk9.drop 196)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 196).take 6), hj0]

private theorem depositViewStage_2445_compile :
    Func.compile vaultTable 2445 (depositViewStage) = some (prorataWethVaultCodeChunk9.drop 141 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 141) := by
  rw [depositViewStage, compile_prepend, previewRedeemStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : previewRedeemStagePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk9.drop 141).take 51 := by
    rw [previewRedeemStagePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk9.drop 196 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 137) : Bytes).length = 709 := by decide +kernel
  have hbranch := compile_branch vaultTable 2496 3209 _ _
    (prorataWethVaultCodeChunk9.drop 196 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 137) [0x5f, 0x5f, 0xfd]
    depositViewAssets_2500_compile (by rw [hlen]) (by decide) (revert_compile_at 3210)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3209 >>> 8).toUInt8, Nat.toUInt8 3209, 0x57] : Bytes) = (prorataWethVaultCodeChunk9.drop 192).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk12.drop 137).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk12.drop 138).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 141).take 51) ++ ((prorataWethVaultCodeChunk9.drop 192).take 4) = (prorataWethVaultCodeChunk9.drop 141).take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9.drop 141) (i := 51) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 141).take 51), hj0]
  have hj1 : ((prorataWethVaultCodeChunk9.drop 141).take 55) ++ (prorataWethVaultCodeChunk9.drop 196) = prorataWethVaultCodeChunk9.drop 141 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 55 (prorataWethVaultCodeChunk9.drop 141)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 141).take 55), hj1]
  have hj2 : (prorataWethVaultCodeChunk12.take 137) ++ ((prorataWethVaultCodeChunk12.drop 137).take 1) = prorataWethVaultCodeChunk12.take 138 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 137) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 137), hj2]
  have hj3 : (prorataWethVaultCodeChunk12.take 138) ++ ((prorataWethVaultCodeChunk12.drop 138).take 3) = prorataWethVaultCodeChunk12.take 141 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 138) (j := 3)).symm
  rw [hj3]

private theorem depositViewReturnSize_2436_compile :
    Func.compile vaultTable 2436 (depositViewReturnSize) = some (prorataWethVaultCodeChunk9.drop 132 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 145) := by
  rw [depositViewReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk9.drop 132).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk9.drop 141 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 141) : Bytes).length = 768 := by decide +kernel
  have hbranch := compile_branch vaultTable 2441 3213 _ _
    (prorataWethVaultCodeChunk9.drop 141 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 141) [0x5f, 0x5f, 0xfd]
    depositViewStage_2445_compile (by rw [hlen]) (by decide) (revert_compile_at 3214)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3213 >>> 8).toUInt8, Nat.toUInt8 3213, 0x57] : Bytes) = (prorataWethVaultCodeChunk9.drop 137).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk12.drop 141).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk12.drop 142).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 132).take 5) ++ ((prorataWethVaultCodeChunk9.drop 137).take 4) = (prorataWethVaultCodeChunk9.drop 132).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9.drop 132) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 132).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk9.drop 132).take 9) ++ (prorataWethVaultCodeChunk9.drop 141) = prorataWethVaultCodeChunk9.drop 132 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk9.drop 132)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 132).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk12.take 141) ++ ((prorataWethVaultCodeChunk12.drop 141).take 1) = prorataWethVaultCodeChunk12.take 142 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 141) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 141), hj2]
  have hj3 : (prorataWethVaultCodeChunk12.take 142) ++ ((prorataWethVaultCodeChunk12.drop 142).take 3) = prorataWethVaultCodeChunk12.take 145 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 142) (j := 3)).symm
  rw [hj3]

private theorem depositViewRead_2408_compile :
    Func.compile vaultTable 2408 (depositViewRead) = some (prorataWethVaultCodeChunk9.drop 104 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 149) := by
  rw [depositViewRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk9.drop 104).take 24 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk9.drop 132 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 145) : Bytes).length = 781 := by decide +kernel
  have hbranch := compile_branch vaultTable 2432 3217 _ _
    (prorataWethVaultCodeChunk9.drop 132 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 145) [0x5f, 0x5f, 0xfd]
    depositViewReturnSize_2436_compile (by rw [hlen]) (by decide) (revert_compile_at 3218)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3217 >>> 8).toUInt8, Nat.toUInt8 3217, 0x57] : Bytes) = (prorataWethVaultCodeChunk9.drop 128).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk12.drop 145).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk12.drop 146).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 104).take 24) ++ ((prorataWethVaultCodeChunk9.drop 128).take 4) = (prorataWethVaultCodeChunk9.drop 104).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9.drop 104) (i := 24) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 104).take 24), hj0]
  have hj1 : ((prorataWethVaultCodeChunk9.drop 104).take 28) ++ (prorataWethVaultCodeChunk9.drop 132) = prorataWethVaultCodeChunk9.drop 104 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 28 (prorataWethVaultCodeChunk9.drop 104)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 104).take 28), hj1]
  have hj2 : (prorataWethVaultCodeChunk12.take 145) ++ ((prorataWethVaultCodeChunk12.drop 145).take 1) = prorataWethVaultCodeChunk12.take 146 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 145) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 145), hj2]
  have hj3 : (prorataWethVaultCodeChunk12.take 146) ++ ((prorataWethVaultCodeChunk12.drop 146).take 3) = prorataWethVaultCodeChunk12.take 149 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 146) (j := 3)).symm
  rw [hj3]

private theorem depositViewStatic_2400_compile :
    Func.compile vaultTable 2400 (depositViewStatic) = some (prorataWethVaultCodeChunk9.drop 96 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 153) := by
  rw [depositViewStatic, compile_prepend, maxDepositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk9.drop 96).take 4 := by
    rw [maxDepositStaticPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk9.drop 104 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 149) : Bytes).length = 813 := by decide +kernel
  have hbranch := compile_branch vaultTable 2404 3221 _ _
    (prorataWethVaultCodeChunk9.drop 104 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 149) [0x5f, 0x5f, 0xfd]
    depositViewRead_2408_compile (by rw [hlen]) (by decide) (revert_compile_at 3222)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3221 >>> 8).toUInt8, Nat.toUInt8 3221, 0x57] : Bytes) = (prorataWethVaultCodeChunk9.drop 100).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk12.drop 149).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk12.drop 150).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 96).take 4) ++ ((prorataWethVaultCodeChunk9.drop 100).take 4) = (prorataWethVaultCodeChunk9.drop 96).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9.drop 96) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 96).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk9.drop 96).take 8) ++ (prorataWethVaultCodeChunk9.drop 104) = prorataWethVaultCodeChunk9.drop 96 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk9.drop 96)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 96).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk12.take 149) ++ ((prorataWethVaultCodeChunk12.drop 149).take 1) = prorataWethVaultCodeChunk12.take 150 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 149) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 149), hj2]
  have hj3 : (prorataWethVaultCodeChunk12.take 150) ++ ((prorataWethVaultCodeChunk12.drop 150).take 3) = prorataWethVaultCodeChunk12.take 153 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 150) (j := 3)).symm
  rw [hj3]

private theorem convertToShares_source_cut : ProrataWethVault.routed 1 ProrataWethVault.convertToShares = nonpayable depositViewStatic := by rfl
private theorem convertToShares_endpoint_compile :
    Func.compile vaultTable 2390 (ProrataWethVault.routed 1 ProrataWethVault.convertToShares) = some (prorataWethVaultCodeChunk9.drop 86 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 153) := by
  rw [convertToShares_source_cut]
  have hcut : nonpayable depositViewStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert depositViewStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 2392 2399 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk9.drop 96 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 153)
    (revert_compile_at 2396) (by rfl) (by decide) depositViewStatic_2400_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (2399 >>> 8).toUInt8, Nat.toUInt8 2399, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk9.drop 86).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (2399 >>> 8).toUInt8, Nat.toUInt8 2399, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 86).take 10) ++ (prorataWethVaultCodeChunk9.drop 96) = prorataWethVaultCodeChunk9.drop 86 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk9.drop 86)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 86).take 10), hj0]

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceAddress0Prefix : Line := arg 0 ++ checkNonAddress
private theorem allowanceAddress0Prefix_size : prefixByteSize allowanceAddress0Prefix = 9 := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceAddress1Prefix : Line := arg 1 ++ checkNonAddress
private theorem allowanceAddress1Prefix_size : prefixByteSize allowanceAddress1Prefix = 9 := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceKeyPrefix : Line := arg 0 ++ mstoreAt 0 ++ arg 1 ++ mstoreAt 1 ++ pushList [64, 0] ++ [keccak256] ++ checkAllowanceSlotCollision
private theorem allowanceKeyPrefix_size : prefixByteSize allowanceKeyPrefix = 27 := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceStorageReturn : Func := sload ::: returnWord

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceKey : Func := allowanceKeyPrefix +++ Func.branch allowanceStorageReturn Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceAddress1 : Func := allowanceAddress1Prefix +++ Func.branch allowanceKey Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceAddress0 : Func := allowanceAddress0Prefix +++ Func.branch allowanceAddress1 Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def allowanceStatic : Func := depositStaticPrefix +++ Func.branch allowanceAddress0 Func.revert

private theorem allowanceStorageReturn_1002_compile :
    Func.compile vaultTable 1002 allowanceStorageReturn = some ((prorataWethVaultCodeChunk3.drop 234).take 7) := by rfl

private theorem allowanceKey_971_compile :
    Func.compile vaultTable 971 (allowanceKey) = some ((prorataWethVaultCodeChunk3.drop 203).take 42) := by
  rw [allowanceKey, compile_prepend, allowanceKeyPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : allowanceKeyPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk3.drop 203).take 27 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk3.drop 234).take 7) : Bytes).length = 7 := by decide +kernel
  have hbranch := compile_branch vaultTable 998 1009 _ _
    ((prorataWethVaultCodeChunk3.drop 234).take 7) [0x5f, 0x5f, 0xfd]
    allowanceStorageReturn_1002_compile (by rw [hlen]) (by decide) (revert_compile_at 1010)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1009 >>> 8).toUInt8, Nat.toUInt8 1009, 0x57] : Bytes) = (prorataWethVaultCodeChunk3.drop 230).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 241).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk3.drop 242).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk3.drop 203).take 27) ++ ((prorataWethVaultCodeChunk3.drop 230).take 4) = (prorataWethVaultCodeChunk3.drop 203).take 31 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 203) (i := 27) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 203).take 27), hj0]
  have hj1 : ((prorataWethVaultCodeChunk3.drop 203).take 31) ++ ((prorataWethVaultCodeChunk3.drop 234).take 7) = (prorataWethVaultCodeChunk3.drop 203).take 38 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 203) (i := 31) (j := 7)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 203).take 31), hj1]
  have hj2 : ((prorataWethVaultCodeChunk3.drop 203).take 38) ++ ((prorataWethVaultCodeChunk3.drop 241).take 1) = (prorataWethVaultCodeChunk3.drop 203).take 39 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 203) (i := 38) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 203).take 38), hj2]
  have hj3 : ((prorataWethVaultCodeChunk3.drop 203).take 39) ++ ((prorataWethVaultCodeChunk3.drop 242).take 3) = (prorataWethVaultCodeChunk3.drop 203).take 42 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 203) (i := 39) (j := 3)).symm
  rw [hj3]

private theorem allowanceAddress1_958_compile :
    Func.compile vaultTable 958 (allowanceAddress1) = some ((prorataWethVaultCodeChunk3.drop 190).take 59) := by
  rw [allowanceAddress1, compile_prepend, allowanceAddress1Prefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : allowanceAddress1Prefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk3.drop 190).take 9 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk3.drop 203).take 42) : Bytes).length = 42 := by decide +kernel
  have hbranch := compile_branch vaultTable 967 1013 _ _
    ((prorataWethVaultCodeChunk3.drop 203).take 42) [0x5f, 0x5f, 0xfd]
    allowanceKey_971_compile (by rw [hlen]) (by decide) (revert_compile_at 1014)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1013 >>> 8).toUInt8, Nat.toUInt8 1013, 0x57] : Bytes) = (prorataWethVaultCodeChunk3.drop 199).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 245).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk3.drop 246).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk3.drop 190).take 9) ++ ((prorataWethVaultCodeChunk3.drop 199).take 4) = (prorataWethVaultCodeChunk3.drop 190).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 190) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 190).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk3.drop 190).take 13) ++ ((prorataWethVaultCodeChunk3.drop 203).take 42) = (prorataWethVaultCodeChunk3.drop 190).take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 190) (i := 13) (j := 42)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 190).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk3.drop 190).take 55) ++ ((prorataWethVaultCodeChunk3.drop 245).take 1) = (prorataWethVaultCodeChunk3.drop 190).take 56 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 190) (i := 55) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 190).take 55), hj2]
  have hj3 : ((prorataWethVaultCodeChunk3.drop 190).take 56) ++ ((prorataWethVaultCodeChunk3.drop 246).take 3) = (prorataWethVaultCodeChunk3.drop 190).take 59 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 190) (i := 56) (j := 3)).symm
  rw [hj3]

private theorem allowanceAddress0_945_compile :
    Func.compile vaultTable 945 (allowanceAddress0) = some ((prorataWethVaultCodeChunk3.drop 177).take 76) := by
  rw [allowanceAddress0, compile_prepend, allowanceAddress0Prefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : allowanceAddress0Prefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk3.drop 177).take 9 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk3.drop 190).take 59) : Bytes).length = 59 := by decide +kernel
  have hbranch := compile_branch vaultTable 954 1017 _ _
    ((prorataWethVaultCodeChunk3.drop 190).take 59) [0x5f, 0x5f, 0xfd]
    allowanceAddress1_958_compile (by rw [hlen]) (by decide) (revert_compile_at 1018)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1017 >>> 8).toUInt8, Nat.toUInt8 1017, 0x57] : Bytes) = (prorataWethVaultCodeChunk3.drop 186).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 249).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk3.drop 250).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk3.drop 177).take 9) ++ ((prorataWethVaultCodeChunk3.drop 186).take 4) = (prorataWethVaultCodeChunk3.drop 177).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 177) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 177).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk3.drop 177).take 13) ++ ((prorataWethVaultCodeChunk3.drop 190).take 59) = (prorataWethVaultCodeChunk3.drop 177).take 72 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 177) (i := 13) (j := 59)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 177).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk3.drop 177).take 72) ++ ((prorataWethVaultCodeChunk3.drop 249).take 1) = (prorataWethVaultCodeChunk3.drop 177).take 73 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 177) (i := 72) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 177).take 72), hj2]
  have hj3 : ((prorataWethVaultCodeChunk3.drop 177).take 73) ++ ((prorataWethVaultCodeChunk3.drop 250).take 3) = (prorataWethVaultCodeChunk3.drop 177).take 76 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 177) (i := 73) (j := 3)).symm
  rw [hj3]

private theorem allowanceStatic_937_compile :
    Func.compile vaultTable 937 (allowanceStatic) = some (prorataWethVaultCodeChunk3.drop 169 ++ prorataWethVaultCodeChunk4.take 1) := by
  rw [allowanceStatic, compile_prepend, depositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : depositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk3.drop 169).take 4 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk3.drop 177).take 76) : Bytes).length = 76 := by decide +kernel
  have hbranch := compile_branch vaultTable 941 1021 _ _
    ((prorataWethVaultCodeChunk3.drop 177).take 76) [0x5f, 0x5f, 0xfd]
    allowanceAddress0_945_compile (by rw [hlen]) (by decide) (revert_compile_at 1022)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1021 >>> 8).toUInt8, Nat.toUInt8 1021, 0x57] : Bytes) = (prorataWethVaultCodeChunk3.drop 173).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 253).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = prorataWethVaultCodeChunk3.drop 254 ++ prorataWethVaultCodeChunk4.take 1 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk3.drop 169).take 4) ++ ((prorataWethVaultCodeChunk3.drop 173).take 4) = (prorataWethVaultCodeChunk3.drop 169).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 169) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 169).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk3.drop 169).take 8) ++ ((prorataWethVaultCodeChunk3.drop 177).take 76) = (prorataWethVaultCodeChunk3.drop 169).take 84 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 169) (i := 8) (j := 76)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 169).take 8), hj1]
  have hj2 : ((prorataWethVaultCodeChunk3.drop 169).take 84) ++ ((prorataWethVaultCodeChunk3.drop 253).take 1) = (prorataWethVaultCodeChunk3.drop 169).take 85 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3.drop 169) (i := 84) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 169).take 84), hj2]
  have hj3 : ((prorataWethVaultCodeChunk3.drop 169).take 85) ++ (prorataWethVaultCodeChunk3.drop 254) = prorataWethVaultCodeChunk3.drop 169 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 85 (prorataWethVaultCodeChunk3.drop 169)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 169).take 85), hj3]

private theorem boundedAllowance_source_cut : ProrataWethVault.routed 2 ProrataWethVault.allowance = nonpayable allowanceStatic := by rfl
private theorem boundedAllowance_endpoint_compile :
    Func.compile vaultTable 927 (ProrataWethVault.routed 2 ProrataWethVault.allowance) = some (prorataWethVaultCodeChunk3.drop 159 ++ prorataWethVaultCodeChunk4.take 1) := by
  rw [boundedAllowance_source_cut]
  have hcut : nonpayable allowanceStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert allowanceStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 929 936 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk3.drop 169 ++ prorataWethVaultCodeChunk4.take 1)
    (revert_compile_at 933) (by rfl) (by decide) allowanceStatic_937_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (936 >>> 8).toUInt8, Nat.toUInt8 936, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk3.drop 159).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (936 >>> 8).toUInt8, Nat.toUInt8 936, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk3.drop 159).take 10) ++ (prorataWethVaultCodeChunk3.drop 169) = prorataWethVaultCodeChunk3.drop 159 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk3.drop 159)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 159).take 10), hj0]

open ProrataWethVault Jaune.Ninst Ninst in
private def directTransferStage : Func := approveStagePrefix +++ .call transferFromAfterAllowanceSlot

open ProrataWethVault Jaune.Ninst Ninst in
private def directTransferNonzero : Func := vaultNonzeroPrefix +++ Func.branch directTransferStage Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def directTransferAddress : Func := vaultAddress0Prefix +++ Func.branch directTransferNonzero Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def directTransferCaller : Func := vaultCallerPrefix +++ Func.branch directTransferAddress Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def directTransferStatic : Func := depositStaticPrefix +++ Func.branch directTransferCaller Func.revert

private theorem directTransferSlot_7776_compile :
    Func.compile vaultTable 7776 (Func.call ProrataWethVault.transferFromAfterAllowanceSlot) =
      some ((prorataWethVaultCodeChunk30.drop 96).take 4) := by
  rw [transferStaged_slot_compile_at]
  rfl

private theorem directTransferStage_7757_compile :
    Func.compile vaultTable 7757 (directTransferStage) = some ((prorataWethVaultCodeChunk30.drop 77).take 23) := by
  have hb0 : approveStagePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk30.drop 77).take 19 := by
    rfl
  rw [directTransferStage]
  rw [compile_prepend, approveStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [directTransferSlot_7776_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 77).take 19) ++ ((prorataWethVaultCodeChunk30.drop 96).take 4) = (prorataWethVaultCodeChunk30.drop 77).take 23 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 77) (i := 19) (j := 4)).symm
  rw [hj0]

private theorem directTransferNonzero_7752_compile :
    Func.compile vaultTable 7752 (directTransferNonzero) = some ((prorataWethVaultCodeChunk30.drop 72).take 32) := by
  rw [directTransferNonzero, compile_prepend, vaultNonzeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : vaultNonzeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk30.drop 72).take 1 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk30.drop 77).take 23) : Bytes).length = 23 := by decide +kernel
  have hbranch := compile_branch vaultTable 7753 7780 _ _
    ((prorataWethVaultCodeChunk30.drop 77).take 23) [0x5f, 0x5f, 0xfd]
    directTransferStage_7757_compile (by rw [hlen]) (by decide) (revert_compile_at 7781)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7780 >>> 8).toUInt8, Nat.toUInt8 7780, 0x57] : Bytes) = (prorataWethVaultCodeChunk30.drop 73).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 100).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk30.drop 101).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 72).take 1) ++ ((prorataWethVaultCodeChunk30.drop 73).take 4) = (prorataWethVaultCodeChunk30.drop 72).take 5 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 72) (i := 1) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 72).take 1), hj0]
  have hj1 : ((prorataWethVaultCodeChunk30.drop 72).take 5) ++ ((prorataWethVaultCodeChunk30.drop 77).take 23) = (prorataWethVaultCodeChunk30.drop 72).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 72) (i := 5) (j := 23)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 72).take 5), hj1]
  have hj2 : ((prorataWethVaultCodeChunk30.drop 72).take 28) ++ ((prorataWethVaultCodeChunk30.drop 100).take 1) = (prorataWethVaultCodeChunk30.drop 72).take 29 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 72) (i := 28) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 72).take 28), hj2]
  have hj3 : ((prorataWethVaultCodeChunk30.drop 72).take 29) ++ ((prorataWethVaultCodeChunk30.drop 101).take 3) = (prorataWethVaultCodeChunk30.drop 72).take 32 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 72) (i := 29) (j := 3)).symm
  rw [hj3]

private theorem directTransferAddress_7738_compile :
    Func.compile vaultTable 7738 (directTransferAddress) = some ((prorataWethVaultCodeChunk30.drop 58).take 50) := by
  rw [directTransferAddress, compile_prepend, vaultAddress0Prefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : vaultAddress0Prefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk30.drop 58).take 10 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk30.drop 72).take 32) : Bytes).length = 32 := by decide +kernel
  have hbranch := compile_branch vaultTable 7748 7784 _ _
    ((prorataWethVaultCodeChunk30.drop 72).take 32) [0x5f, 0x5f, 0xfd]
    directTransferNonzero_7752_compile (by rw [hlen]) (by decide) (revert_compile_at 7785)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7784 >>> 8).toUInt8, Nat.toUInt8 7784, 0x57] : Bytes) = (prorataWethVaultCodeChunk30.drop 68).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 104).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk30.drop 105).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 58).take 10) ++ ((prorataWethVaultCodeChunk30.drop 68).take 4) = (prorataWethVaultCodeChunk30.drop 58).take 14 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 58) (i := 10) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 58).take 10), hj0]
  have hj1 : ((prorataWethVaultCodeChunk30.drop 58).take 14) ++ ((prorataWethVaultCodeChunk30.drop 72).take 32) = (prorataWethVaultCodeChunk30.drop 58).take 46 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 58) (i := 14) (j := 32)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 58).take 14), hj1]
  have hj2 : ((prorataWethVaultCodeChunk30.drop 58).take 46) ++ ((prorataWethVaultCodeChunk30.drop 104).take 1) = (prorataWethVaultCodeChunk30.drop 58).take 47 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 58) (i := 46) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 58).take 46), hj2]
  have hj3 : ((prorataWethVaultCodeChunk30.drop 58).take 47) ++ ((prorataWethVaultCodeChunk30.drop 105).take 3) = (prorataWethVaultCodeChunk30.drop 58).take 50 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 58) (i := 47) (j := 3)).symm
  rw [hj3]

private theorem directTransferCaller_7732_compile :
    Func.compile vaultTable 7732 (directTransferCaller) = some ((prorataWethVaultCodeChunk30.drop 52).take 60) := by
  rw [directTransferCaller, compile_prepend, vaultCallerPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : vaultCallerPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk30.drop 52).take 2 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk30.drop 58).take 50) : Bytes).length = 50 := by decide +kernel
  have hbranch := compile_branch vaultTable 7734 7788 _ _
    ((prorataWethVaultCodeChunk30.drop 58).take 50) [0x5f, 0x5f, 0xfd]
    directTransferAddress_7738_compile (by rw [hlen]) (by decide) (revert_compile_at 7789)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7788 >>> 8).toUInt8, Nat.toUInt8 7788, 0x57] : Bytes) = (prorataWethVaultCodeChunk30.drop 54).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 108).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk30.drop 109).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 52).take 2) ++ ((prorataWethVaultCodeChunk30.drop 54).take 4) = (prorataWethVaultCodeChunk30.drop 52).take 6 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 52) (i := 2) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 52).take 2), hj0]
  have hj1 : ((prorataWethVaultCodeChunk30.drop 52).take 6) ++ ((prorataWethVaultCodeChunk30.drop 58).take 50) = (prorataWethVaultCodeChunk30.drop 52).take 56 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 52) (i := 6) (j := 50)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 52).take 6), hj1]
  have hj2 : ((prorataWethVaultCodeChunk30.drop 52).take 56) ++ ((prorataWethVaultCodeChunk30.drop 108).take 1) = (prorataWethVaultCodeChunk30.drop 52).take 57 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 52) (i := 56) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 52).take 56), hj2]
  have hj3 : ((prorataWethVaultCodeChunk30.drop 52).take 57) ++ ((prorataWethVaultCodeChunk30.drop 109).take 3) = (prorataWethVaultCodeChunk30.drop 52).take 60 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 52) (i := 57) (j := 3)).symm
  rw [hj3]

private theorem directTransferStatic_7724_compile :
    Func.compile vaultTable 7724 (directTransferStatic) = some ((prorataWethVaultCodeChunk30.drop 44).take 72) := by
  rw [directTransferStatic, compile_prepend, depositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : depositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk30.drop 44).take 4 := by
    rfl
  have hlen : (((prorataWethVaultCodeChunk30.drop 52).take 60) : Bytes).length = 60 := by decide +kernel
  have hbranch := compile_branch vaultTable 7728 7792 _ _
    ((prorataWethVaultCodeChunk30.drop 52).take 60) [0x5f, 0x5f, 0xfd]
    directTransferCaller_7732_compile (by rw [hlen]) (by decide) (revert_compile_at 7793)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7792 >>> 8).toUInt8, Nat.toUInt8 7792, 0x57] : Bytes) = (prorataWethVaultCodeChunk30.drop 48).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 112).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk30.drop 113).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 44).take 4) ++ ((prorataWethVaultCodeChunk30.drop 48).take 4) = (prorataWethVaultCodeChunk30.drop 44).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 44) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 44).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk30.drop 44).take 8) ++ ((prorataWethVaultCodeChunk30.drop 52).take 60) = (prorataWethVaultCodeChunk30.drop 44).take 68 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 44) (i := 8) (j := 60)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 44).take 8), hj1]
  have hj2 : ((prorataWethVaultCodeChunk30.drop 44).take 68) ++ ((prorataWethVaultCodeChunk30.drop 112).take 1) = (prorataWethVaultCodeChunk30.drop 44).take 69 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 44) (i := 68) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 44).take 68), hj2]
  have hj3 : ((prorataWethVaultCodeChunk30.drop 44).take 69) ++ ((prorataWethVaultCodeChunk30.drop 113).take 3) = (prorataWethVaultCodeChunk30.drop 44).take 72 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 44) (i := 69) (j := 3)).symm
  rw [hj3]

private theorem directTransfer_source_cut : ProrataWethVault.routed 2 ProrataWethVault.transfer = nonpayable directTransferStatic := by rfl
private theorem directTransfer_endpoint_compile :
    Func.compile vaultTable 7714 (ProrataWethVault.routed 2 ProrataWethVault.transfer) = some ((prorataWethVaultCodeChunk30.drop 34).take 82) := by
  rw [directTransfer_source_cut]
  have hcut : nonpayable directTransferStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert directTransferStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 7716 7723 _ _
    [0x5f, 0x5f, 0xfd] ((prorataWethVaultCodeChunk30.drop 44).take 72)
    (revert_compile_at 7720) (by rfl) (by decide) directTransferStatic_7724_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (7723 >>> 8).toUInt8, Nat.toUInt8 7723, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk30.drop 34).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (7723 >>> 8).toUInt8, Nat.toUInt8 7723, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 34).take 10) ++ ((prorataWethVaultCodeChunk30.drop 44).take 72) = (prorataWethVaultCodeChunk30.drop 34).take 82 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 34) (i := 10) (j := 72)).symm
  rw [hj0]

private theorem allowance_endpoint_compile :
    Func.compile vaultTable 927 (ProrataWethVault.routed 2 ProrataWethVault.allowance) =
      some (prorataWethVaultCodeChunk3.drop 159 ++ prorataWethVaultCodeChunk4.take 1) := by
  exact boundedAllowance_endpoint_compile
private theorem maxRedeem_endpoint_compile :
    Func.compile vaultTable 1041 (ProrataWethVault.routed 1 ProrataWethVault.maxRedeem) =
      some ((prorataWethVaultCodeChunk4.drop 17).take 49) := by rfl
private theorem symbol_endpoint_compile :
    Func.compile vaultTable 7823 (ProrataWethVault.routed 0 ProrataWethVault.symbol) =
      some ((prorataWethVaultCodeChunk30.drop 143).take 48) := by rfl
private theorem transfer_endpoint_compile :
    Func.compile vaultTable 7714 (ProrataWethVault.routed 2 ProrataWethVault.transfer) =
      some ((prorataWethVaultCodeChunk30.drop 34).take 82) := by
  exact directTransfer_endpoint_compile

private theorem previewDepositSelector_value : selector "previewDeposit" [.uint256] = (0xef8b30f7 : B256) := by decide +kernel

private theorem allowanceSelector_value : selector "allowance" [.address, .address] = (0xdd62ed3e : B256) := by decide +kernel

private theorem maxRedeemSelector_value : selector "maxRedeem" [.address] = (0xd905777e : B256) := by decide +kernel

private theorem previewDeposit_dispatch_compile :
    Func.compile vaultTable 50 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightRightB.drop 2))) = some (prorataWethVaultCodeChunk0.drop 50 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 132) := by
  rw [previewDeposit_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "previewDeposit" [.uint256]) (ProrataWethVault.routed 1 ProrataWethVault.previewDeposit)) =
      ([Ninst.pushB256 (selector "previewDeposit" [.uint256]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 1 ProrataWethVault.previewDeposit) := by rfl
  rw [hcut, compile_prepend, previewDepositSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xef8b30f7, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 56 64 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk0.drop 65 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 132)
    (revert_slot_compile_at 60) (by rfl) (by decide) previewDeposit_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xef8b30f7, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xef, 0x8b, 0x30, 0xf7, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xef, 0x8b, 0x30, 0xf7, 0x14] : Bytes) ++
      ([0x61, (64 >>> 8).toUInt8, Nat.toUInt8 64, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk0.drop 50).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (64 >>> 8).toUInt8, Nat.toUInt8 64, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xef, 0x8b, 0x30, 0xf7, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 50).take 15) ++ (prorataWethVaultCodeChunk0.drop 65) = prorataWethVaultCodeChunk0.drop 50 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk0.drop 50)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 50).take 15), hj0]

private theorem allowance_dispatch_compile :
    Func.compile vaultTable 912 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightBPair.drop 1))) = some (prorataWethVaultCodeChunk3.drop 144 ++ prorataWethVaultCodeChunk4.take 1) := by
  rw [allowance_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "allowance" [.address, .address]) (ProrataWethVault.routed 2 ProrataWethVault.allowance)) =
      ([Ninst.pushB256 (selector "allowance" [.address, .address]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 2 ProrataWethVault.allowance) := by rfl
  rw [hcut, compile_prepend, allowanceSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xdd62ed3e, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 918 926 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk3.drop 159 ++ prorataWethVaultCodeChunk4.take 1)
    (revert_slot_compile_at 922) (by rfl) (by decide) allowance_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xdd62ed3e, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xdd, 0x62, 0xed, 0x3e, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xdd, 0x62, 0xed, 0x3e, 0x14] : Bytes) ++
      ([0x61, (926 >>> 8).toUInt8, Nat.toUInt8 926, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk3.drop 144).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (926 >>> 8).toUInt8, Nat.toUInt8 926, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xdd, 0x62, 0xed, 0x3e, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk3.drop 144).take 15) ++ (prorataWethVaultCodeChunk3.drop 159) = prorataWethVaultCodeChunk3.drop 144 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk3.drop 144)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 144).take 15), hj0]

private theorem maxRedeem_dispatch_compile :
    Func.compile vaultTable 1026 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightBPair.take 1))) = some ((prorataWethVaultCodeChunk4.drop 2).take 64) := by
  rw [maxRedeem_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "maxRedeem" [.address]) (ProrataWethVault.routed 1 ProrataWethVault.maxRedeem)) =
      ([Ninst.pushB256 (selector "maxRedeem" [.address]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 1 ProrataWethVault.maxRedeem) := by rfl
  rw [hcut, compile_prepend, maxRedeemSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xd905777e, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 1032 1040 _ _
    [0x61, 0x3d, 0x2f, 0x56] ((prorataWethVaultCodeChunk4.drop 17).take 49)
    (revert_slot_compile_at 1036) (by rfl) (by decide) maxRedeem_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xd905777e, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xd9, 0x5, 0x77, 0x7e, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xd9, 0x5, 0x77, 0x7e, 0x14] : Bytes) ++
      ([0x61, (1040 >>> 8).toUInt8, Nat.toUInt8 1040, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk4.drop 2).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (1040 >>> 8).toUInt8, Nat.toUInt8 1040, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xd9, 0x5, 0x77, 0x7e, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 2).take 15) ++ ((prorataWethVaultCodeChunk4.drop 17).take 49) = (prorataWethVaultCodeChunk4.drop 2).take 64 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4.drop 2) (i := 15) (j := 49)).symm
  rw [hj0]

private theorem rootRightRightBPair_dispatch_compile :
    Func.compile vaultTable 901 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightRightBPair)) = some (prorataWethVaultCodeChunk3.drop 133 ++ prorataWethVaultCodeChunk4.take 66) := by
  rw [rootRightRightBPair_dispatch_node]
  have hcut : dispatchNode (selector "allowance" [.address, .address]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightBPair.take 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightBPair.drop 1))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "allowance" [.address, .address]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightBPair.drop 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightBPair.take 1))) := by rfl
  rw [hcut, compile_prepend, allowanceSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xdd62ed3e, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk3.drop 144 ++ prorataWethVaultCodeChunk4.take 1).length = 113 := by decide +kernel
  have hbranch := compile_branch vaultTable 908 1025 _ _
    (prorataWethVaultCodeChunk3.drop 144 ++ prorataWethVaultCodeChunk4.take 1) ((prorataWethVaultCodeChunk4.drop 2).take 64)
    allowance_dispatch_compile (by rw [hlen]) (by decide) maxRedeem_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xdd62ed3e, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xdd, 0x62, 0xed, 0x3e, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk4.drop 1).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xdd, 0x62, 0xed, 0x3e, 0x11] : Bytes) ++
      ([0x61, (1025 >>> 8).toUInt8, Nat.toUInt8 1025, 0x57] : Bytes) = (prorataWethVaultCodeChunk3.drop 133).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xdd, 0x62, 0xed, 0x3e, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk3.drop 133).take 11) ++ (prorataWethVaultCodeChunk3.drop 144) = prorataWethVaultCodeChunk3.drop 133 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk3.drop 133)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk3.drop 133).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk4.take 1) ++ ((prorataWethVaultCodeChunk4.drop 1).take 1) = prorataWethVaultCodeChunk4.take 2 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4) (i := 1) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk4.take 1), hj1]
  have hj2 : (prorataWethVaultCodeChunk4.take 2) ++ ((prorataWethVaultCodeChunk4.drop 2).take 64) = prorataWethVaultCodeChunk4.take 66 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4) (i := 2) (j := 64)).symm
  rw [hj2]

private theorem rootRightRightB_dispatch_compile :
    Func.compile vaultTable 39 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightRightB)) = some (prorataWethVaultCodeChunk0.drop 39 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4.take 66) := by
  rw [rootRightRightB_dispatch_node]
  have hcut : dispatchNode (selector "previewDeposit" [.uint256]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightRightBPair)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightRightB.drop 2))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "previewDeposit" [.uint256]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightRightB.drop 2))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightRightBPair)) := by rfl
  rw [hcut, compile_prepend, previewDepositSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xef8b30f7, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk0.drop 50 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 132).length = 850 := by decide +kernel
  have hbranch := compile_branch vaultTable 46 900 _ _
    (prorataWethVaultCodeChunk0.drop 50 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3.take 132) (prorataWethVaultCodeChunk3.drop 133 ++ prorataWethVaultCodeChunk4.take 66)
    previewDeposit_dispatch_compile (by rw [hlen]) (by decide) rootRightRightBPair_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xef8b30f7, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xef, 0x8b, 0x30, 0xf7, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk3.drop 132).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xef, 0x8b, 0x30, 0xf7, 0x11] : Bytes) ++
      ([0x61, (900 >>> 8).toUInt8, Nat.toUInt8 900, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 39).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xef, 0x8b, 0x30, 0xf7, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 39).take 11) ++ (prorataWethVaultCodeChunk0.drop 50) = prorataWethVaultCodeChunk0.drop 39 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk0.drop 39)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 39).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk3.take 132) ++ ((prorataWethVaultCodeChunk3.drop 132).take 1) = prorataWethVaultCodeChunk3.take 133 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk3) (i := 132) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 132), hj1]
  have hj2 : (prorataWethVaultCodeChunk3.take 133) ++ (prorataWethVaultCodeChunk3.drop 133) = prorataWethVaultCodeChunk3 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 133 (prorataWethVaultCodeChunk3)
  rw [← List.append_assoc (prorataWethVaultCodeChunk3.take 133), hj2]

private theorem previewMintFinish_7042_compile :
    Func.compile vaultTable 7042 (ProrataWethVault.finishQuotient .up ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk27.drop 130).take 40) := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, isMax, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem previewMintWideCore_6695_compile :
    Func.compile vaultTable 6695 (ProrataWethVault.divideWideCore .up ProrataWethVault.returnWordSlot) =
      some (prorataWethVaultCodeChunk26.drop 39 ++ prorataWethVaultCodeChunk27.take 170) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk26.drop 39).take 117 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk26.drop 156).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = prorataWethVaultCodeChunk26.drop 247 ++ prorataWethVaultCodeChunk27.take 117 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = prorataWethVaultCodeChunk26.drop 247 ++ prorataWethVaultCodeChunk27.take 54 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk27.drop 54).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : (prorataWethVaultCodeChunk27.take 54) ++ ((prorataWethVaultCodeChunk27.drop 54).take 63) = prorataWethVaultCodeChunk27.take 117 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk27) (i := 54) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk27.drop 117).take 13 := by rfl
  have hcomp := divideWideCore_compile_from_finish 6695 .up ProrataWethVault.returnWordSlot
    ((prorataWethVaultCodeChunk27.drop 130).take 40) previewMintFinish_7042_compile
  rw [hcomp, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk26.drop 39).take 117) ++ ((prorataWethVaultCodeChunk26.drop 156).take 91) = (prorataWethVaultCodeChunk26.drop 39).take 208 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk26.drop 39) (i := 117) (j := 91)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 39).take 117), hj0]
  have hj1 : ((prorataWethVaultCodeChunk26.drop 39).take 208) ++ (prorataWethVaultCodeChunk26.drop 247) = prorataWethVaultCodeChunk26.drop 39 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 208 (prorataWethVaultCodeChunk26.drop 39)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 39).take 208), hj1]
  have hj2 : (prorataWethVaultCodeChunk27.take 117) ++ ((prorataWethVaultCodeChunk27.drop 117).take 13) = prorataWethVaultCodeChunk27.take 130 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk27) (i := 117) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk27.take 117), hj2]
  have hj3 : (prorataWethVaultCodeChunk27.take 130) ++ ((prorataWethVaultCodeChunk27.drop 130).take 40) = prorataWethVaultCodeChunk27.take 170 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk27) (i := 130) (j := 40)).symm
  rw [hj3]

private theorem previewMintSimple_7083_compile :
    Func.compile vaultTable 7083 (ProrataWethVault.divideSimple .up ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk27.drop 171).take 66) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, isMax, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem previewMintWide_6678_compile :
    Func.compile vaultTable 6678 (ProrataWethVault.divideWide .up ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk26.drop 22 ++ prorataWethVaultCodeChunk27.take 170) := by
  rw [divideWide_up_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk26.drop 22).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 6687 6694 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk26.drop 39 ++ prorataWethVaultCodeChunk27.take 170)
    (revert_compile_at 6691) (by rw [hlen]) (by decide) previewMintWideCore_6695_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (6694 >>> 8).toUInt8, Nat.toUInt8 6694, 0x57] : Bytes) = (prorataWethVaultCodeChunk26.drop 31).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk26.drop 38).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk26.drop 35).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk26.drop 22).take 9) ++ ((prorataWethVaultCodeChunk26.drop 31).take 4) = (prorataWethVaultCodeChunk26.drop 22).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk26.drop 22) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 22).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk26.drop 22).take 13) ++ ((prorataWethVaultCodeChunk26.drop 35).take 3) = (prorataWethVaultCodeChunk26.drop 22).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk26.drop 22) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 22).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk26.drop 22).take 16) ++ ((prorataWethVaultCodeChunk26.drop 38).take 1) = (prorataWethVaultCodeChunk26.drop 22).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk26.drop 22) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 22).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk26.drop 22).take 17) ++ (prorataWethVaultCodeChunk26.drop 39) = prorataWethVaultCodeChunk26.drop 22 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk26.drop 22)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 22).take 17), hj3]

private theorem previewMintNonzero_6669_compile :
    Func.compile vaultTable 6669 (divide512NonzeroUp) = some (prorataWethVaultCodeChunk26.drop 13 ++ prorataWethVaultCodeChunk27.take 237) := by
  rw [divide512NonzeroUp, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk26.drop 13).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk26.drop 22 ++ prorataWethVaultCodeChunk27.take 170) : Bytes).length = 404 := by decide +kernel
  have hbranch := compile_branch vaultTable 6674 7082 _ _
    (prorataWethVaultCodeChunk26.drop 22 ++ prorataWethVaultCodeChunk27.take 170) ((prorataWethVaultCodeChunk27.drop 171).take 66)
    previewMintWide_6678_compile (by rw [hlen]) (by decide) previewMintSimple_7083_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7082 >>> 8).toUInt8, Nat.toUInt8 7082, 0x57] : Bytes) = (prorataWethVaultCodeChunk26.drop 18).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk27.drop 170).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk26.drop 13).take 5) ++ ((prorataWethVaultCodeChunk26.drop 18).take 4) = (prorataWethVaultCodeChunk26.drop 13).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk26.drop 13) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 13).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk26.drop 13).take 9) ++ (prorataWethVaultCodeChunk26.drop 22) = prorataWethVaultCodeChunk26.drop 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk26.drop 13)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 13).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk27.take 170) ++ ((prorataWethVaultCodeChunk27.drop 170).take 1) = prorataWethVaultCodeChunk27.take 171 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk27) (i := 170) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk27.take 170), hj2]
  have hj3 : (prorataWethVaultCodeChunk27.take 171) ++ ((prorataWethVaultCodeChunk27.drop 171).take 66) = prorataWethVaultCodeChunk27.take 237 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk27) (i := 171) (j := 66)).symm
  rw [hj3]

private theorem previewMintDivide_6660_compile :
    Func.compile vaultTable 6660 (ProrataWethVault.divide512 .up ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk26.drop 4 ++ prorataWethVaultCodeChunk27.take 241) := by
  rw [divide512_up_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk26.drop 4).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk26.drop 13 ++ prorataWethVaultCodeChunk27.take 237) : Bytes).length = 480 := by decide +kernel
  have hbranch := compile_branch vaultTable 6665 7149 _ _
    (prorataWethVaultCodeChunk26.drop 13 ++ prorataWethVaultCodeChunk27.take 237) [0x5f, 0x5f, 0xfd]
    previewMintNonzero_6669_compile (by rw [hlen]) (by decide) (revert_compile_at 7150)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7149 >>> 8).toUInt8, Nat.toUInt8 7149, 0x57] : Bytes) = (prorataWethVaultCodeChunk26.drop 9).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk27.drop 237).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk27.drop 238).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk26.drop 4).take 5) ++ ((prorataWethVaultCodeChunk26.drop 9).take 4) = (prorataWethVaultCodeChunk26.drop 4).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk26.drop 4) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 4).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk26.drop 4).take 9) ++ (prorataWethVaultCodeChunk26.drop 13) = prorataWethVaultCodeChunk26.drop 4 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk26.drop 4)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk26.drop 4).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk27.take 237) ++ ((prorataWethVaultCodeChunk27.drop 237).take 1) = prorataWethVaultCodeChunk27.take 238 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk27) (i := 237) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk27.take 237), hj2]
  have hj3 : (prorataWethVaultCodeChunk27.take 238) ++ ((prorataWethVaultCodeChunk27.drop 238).take 3) = prorataWethVaultCodeChunk27.take 241 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk27) (i := 238) (j := 3)).symm
  rw [hj3]

private theorem previewMintFinish_7560_compile :
    Func.compile vaultTable 7560 (ProrataWethVault.finishQuotient .up ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk29.drop 136).take 40) := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, isMax, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem previewMintWideCore_7213_compile :
    Func.compile vaultTable 7213 (ProrataWethVault.divideWideCore .up ProrataWethVault.returnWordSlot) =
      some (prorataWethVaultCodeChunk28.drop 45 ++ prorataWethVaultCodeChunk29.take 176) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk28.drop 45).take 117 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk28.drop 162).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = prorataWethVaultCodeChunk28.drop 253 ++ prorataWethVaultCodeChunk29.take 123 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = prorataWethVaultCodeChunk28.drop 253 ++ prorataWethVaultCodeChunk29.take 60 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk29.drop 60).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : (prorataWethVaultCodeChunk29.take 60) ++ ((prorataWethVaultCodeChunk29.drop 60).take 63) = prorataWethVaultCodeChunk29.take 123 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk29) (i := 60) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk29.drop 123).take 13 := by rfl
  have hcomp := divideWideCore_compile_from_finish 7213 .up ProrataWethVault.returnWordSlot
    ((prorataWethVaultCodeChunk29.drop 136).take 40) previewMintFinish_7560_compile
  rw [hcomp, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk28.drop 45).take 117) ++ ((prorataWethVaultCodeChunk28.drop 162).take 91) = (prorataWethVaultCodeChunk28.drop 45).take 208 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk28.drop 45) (i := 117) (j := 91)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 45).take 117), hj0]
  have hj1 : ((prorataWethVaultCodeChunk28.drop 45).take 208) ++ (prorataWethVaultCodeChunk28.drop 253) = prorataWethVaultCodeChunk28.drop 45 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 208 (prorataWethVaultCodeChunk28.drop 45)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 45).take 208), hj1]
  have hj2 : (prorataWethVaultCodeChunk29.take 123) ++ ((prorataWethVaultCodeChunk29.drop 123).take 13) = prorataWethVaultCodeChunk29.take 136 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 123) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk29.take 123), hj2]
  have hj3 : (prorataWethVaultCodeChunk29.take 136) ++ ((prorataWethVaultCodeChunk29.drop 136).take 40) = prorataWethVaultCodeChunk29.take 176 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 136) (j := 40)).symm
  rw [hj3]

private theorem previewMintSimple_7601_compile :
    Func.compile vaultTable 7601 (ProrataWethVault.divideSimple .up ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk29.drop 177).take 66) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, isMax, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem previewMintWide_7196_compile :
    Func.compile vaultTable 7196 (ProrataWethVault.divideWide .up ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk28.drop 28 ++ prorataWethVaultCodeChunk29.take 176) := by
  rw [divideWide_up_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk28.drop 28).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 7205 7212 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk28.drop 45 ++ prorataWethVaultCodeChunk29.take 176)
    (revert_compile_at 7209) (by rw [hlen]) (by decide) previewMintWideCore_7213_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7212 >>> 8).toUInt8, Nat.toUInt8 7212, 0x57] : Bytes) = (prorataWethVaultCodeChunk28.drop 37).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk28.drop 44).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk28.drop 41).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk28.drop 28).take 9) ++ ((prorataWethVaultCodeChunk28.drop 37).take 4) = (prorataWethVaultCodeChunk28.drop 28).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk28.drop 28) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 28).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk28.drop 28).take 13) ++ ((prorataWethVaultCodeChunk28.drop 41).take 3) = (prorataWethVaultCodeChunk28.drop 28).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk28.drop 28) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 28).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk28.drop 28).take 16) ++ ((prorataWethVaultCodeChunk28.drop 44).take 1) = (prorataWethVaultCodeChunk28.drop 28).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk28.drop 28) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 28).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk28.drop 28).take 17) ++ (prorataWethVaultCodeChunk28.drop 45) = prorataWethVaultCodeChunk28.drop 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk28.drop 28)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 28).take 17), hj3]

private theorem previewMintNonzero_7187_compile :
    Func.compile vaultTable 7187 (divide512NonzeroUp) = some (prorataWethVaultCodeChunk28.drop 19 ++ prorataWethVaultCodeChunk29.take 243) := by
  rw [divide512NonzeroUp, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk28.drop 19).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk28.drop 28 ++ prorataWethVaultCodeChunk29.take 176) : Bytes).length = 404 := by decide +kernel
  have hbranch := compile_branch vaultTable 7192 7600 _ _
    (prorataWethVaultCodeChunk28.drop 28 ++ prorataWethVaultCodeChunk29.take 176) ((prorataWethVaultCodeChunk29.drop 177).take 66)
    previewMintWide_7196_compile (by rw [hlen]) (by decide) previewMintSimple_7601_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7600 >>> 8).toUInt8, Nat.toUInt8 7600, 0x57] : Bytes) = (prorataWethVaultCodeChunk28.drop 24).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk29.drop 176).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk28.drop 19).take 5) ++ ((prorataWethVaultCodeChunk28.drop 24).take 4) = (prorataWethVaultCodeChunk28.drop 19).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk28.drop 19) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 19).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk28.drop 19).take 9) ++ (prorataWethVaultCodeChunk28.drop 28) = prorataWethVaultCodeChunk28.drop 19 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk28.drop 19)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 19).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk29.take 176) ++ ((prorataWethVaultCodeChunk29.drop 176).take 1) = prorataWethVaultCodeChunk29.take 177 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 176) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk29.take 176), hj2]
  have hj3 : (prorataWethVaultCodeChunk29.take 177) ++ ((prorataWethVaultCodeChunk29.drop 177).take 66) = prorataWethVaultCodeChunk29.take 243 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 177) (j := 66)).symm
  rw [hj3]

private theorem previewMintDivide_7178_compile :
    Func.compile vaultTable 7178 (ProrataWethVault.divide512 .up ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk28.drop 10 ++ prorataWethVaultCodeChunk29.take 247) := by
  rw [divide512_up_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk28.drop 10).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk28.drop 19 ++ prorataWethVaultCodeChunk29.take 243) : Bytes).length = 480 := by decide +kernel
  have hbranch := compile_branch vaultTable 7183 7667 _ _
    (prorataWethVaultCodeChunk28.drop 19 ++ prorataWethVaultCodeChunk29.take 243) [0x5f, 0x5f, 0xfd]
    previewMintNonzero_7187_compile (by rw [hlen]) (by decide) (revert_compile_at 7668)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7667 >>> 8).toUInt8, Nat.toUInt8 7667, 0x57] : Bytes) = (prorataWethVaultCodeChunk28.drop 15).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk29.drop 243).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk29.drop 244).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk28.drop 10).take 5) ++ ((prorataWethVaultCodeChunk28.drop 15).take 4) = (prorataWethVaultCodeChunk28.drop 10).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk28.drop 10) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 10).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk28.drop 10).take 9) ++ (prorataWethVaultCodeChunk28.drop 19) = prorataWethVaultCodeChunk28.drop 10 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk28.drop 10)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk28.drop 10).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk29.take 243) ++ ((prorataWethVaultCodeChunk29.drop 243).take 1) = prorataWethVaultCodeChunk29.take 244 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 243) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk29.take 243), hj2]
  have hj3 : (prorataWethVaultCodeChunk29.take 244) ++ ((prorataWethVaultCodeChunk29.drop 244).take 3) = prorataWethVaultCodeChunk29.take 247 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 244) (j := 3)).symm
  rw [hj3]

open ProrataWethVault in
private theorem previewMintMul_source_cut :
    mulDiv (arg 0) stagedAssetFactor stagedDenominator .up returnWordSlot =
      previewRedeemMulStage +++ maxDepositMulRecover +++ divide512 .up returnWordSlot := by rfl
open ProrataWethVault in
private theorem previewMintShift_source_cut :
    shiftedDiv (arg 0) stagedDenominator .up returnWordSlot =
      previewRedeemShiftStage +++ divide512 .up returnWordSlot := by rfl
open ProrataWethVault in
private def previewMintArithmetic : Func :=
  Func.branch (mulDiv (arg 0) stagedAssetFactor stagedDenominator .up returnWordSlot)
    (shiftedDiv (arg 0) stagedDenominator .up returnWordSlot)
private def previewMintAssets : Func := previewRedeemAssetsPrefix +++ previewMintArithmetic
private def previewMintStage : Func := previewRedeemStagePrefix +++ Func.branch previewMintAssets Func.revert
private def previewMintReturnSize : Func := maxDepositReturnSizePrefix +++ Func.branch previewMintStage Func.revert
private def previewMintRead : Func := maxDepositReadPrefix +++ Func.branch previewMintReturnSize Func.revert
private def previewMintStatic : Func := maxDepositStaticPrefix +++ Func.branch previewMintRead Func.revert

private theorem previewMintMul_6532_compile :
    Func.compile vaultTable 6532 (ProrataWethVault.mulDiv (arg 0) ProrataWethVault.stagedAssetFactor ProrataWethVault.stagedDenominator .up ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk25.drop 132 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27.take 241) := by
  have hb0 : previewRedeemMulStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk25.drop 132).take 43 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = prorataWethVaultCodeChunk25.drop 175 ++ prorataWethVaultCodeChunk26.take 4 := by
    rfl
  rw [previewMintMul_source_cut]
  rw [compile_prepend, previewRedeemMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [previewMintDivide_6660_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 132).take 43) ++ (prorataWethVaultCodeChunk25.drop 175) = prorataWethVaultCodeChunk25.drop 132 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 43 (prorataWethVaultCodeChunk25.drop 132)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 132).take 43), hj0]
  have hj1 : (prorataWethVaultCodeChunk26.take 4) ++ (prorataWethVaultCodeChunk26.drop 4) = prorataWethVaultCodeChunk26 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk26)
  rw [← List.append_assoc (prorataWethVaultCodeChunk26.take 4), hj1]

private theorem previewMintShift_7154_compile :
    Func.compile vaultTable 7154 (ProrataWethVault.shiftedDiv (arg 0) ProrataWethVault.stagedDenominator .up ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk27.drop 242 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 247) := by
  have hb0 : previewRedeemShiftStage.flatMap Ninst.toBytes = prorataWethVaultCodeChunk27.drop 242 ++ prorataWethVaultCodeChunk28.take 10 := by
    rfl
  rw [previewMintShift_source_cut]
  rw [compile_prepend, previewRedeemShiftStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [previewMintDivide_7178_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk28.take 10) ++ (prorataWethVaultCodeChunk28.drop 10) = prorataWethVaultCodeChunk28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk28)
  rw [← List.append_assoc (prorataWethVaultCodeChunk28.take 10), hj0]

private theorem previewMintArithmetic_6528_compile :
    Func.compile vaultTable 6528 (previewMintArithmetic) = some (prorataWethVaultCodeChunk25.drop 128 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 247) := by
  rw [previewMintArithmetic]
  have hlen : ((prorataWethVaultCodeChunk25.drop 132 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27.take 241) : Bytes).length = 621 := by decide +kernel
  have hbranch := compile_branch vaultTable 6528 7153 _ _
    (prorataWethVaultCodeChunk25.drop 132 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27.take 241) (prorataWethVaultCodeChunk27.drop 242 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 247)
    previewMintMul_6532_compile (by rw [hlen]) (by decide) previewMintShift_7154_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (7153 >>> 8).toUInt8, Nat.toUInt8 7153, 0x57] : Bytes) = (prorataWethVaultCodeChunk25.drop 128).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk27.drop 241).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 128).take 4) ++ (prorataWethVaultCodeChunk25.drop 132) = prorataWethVaultCodeChunk25.drop 128 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk25.drop 128)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 128).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk27.take 241) ++ ((prorataWethVaultCodeChunk27.drop 241).take 1) = prorataWethVaultCodeChunk27.take 242 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk27) (i := 241) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk27.take 241), hj1]
  have hj2 : (prorataWethVaultCodeChunk27.take 242) ++ (prorataWethVaultCodeChunk27.drop 242) = prorataWethVaultCodeChunk27 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 242 (prorataWethVaultCodeChunk27)
  rw [← List.append_assoc (prorataWethVaultCodeChunk27.take 242), hj2]

private theorem previewMintAssets_6522_compile :
    Func.compile vaultTable 6522 (previewMintAssets) = some (prorataWethVaultCodeChunk25.drop 122 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 247) := by
  have hb0 : previewRedeemAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk25.drop 122).take 6 := by
    rw [previewRedeemAssetsPrefix_bytes]
    rfl
  rw [previewMintAssets]
  rw [compile_prepend, previewRedeemAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [previewMintArithmetic_6528_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 122).take 6) ++ (prorataWethVaultCodeChunk25.drop 128) = prorataWethVaultCodeChunk25.drop 122 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 6 (prorataWethVaultCodeChunk25.drop 122)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 122).take 6), hj0]

private theorem previewMintStage_6467_compile :
    Func.compile vaultTable 6467 (previewMintStage) = some (prorataWethVaultCodeChunk25.drop 67 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 251) := by
  rw [previewMintStage, compile_prepend, previewRedeemStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : previewRedeemStagePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk25.drop 67).take 51 := by
    rw [previewRedeemStagePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk25.drop 122 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 247) : Bytes).length = 1149 := by decide +kernel
  have hbranch := compile_branch vaultTable 6518 7671 _ _
    (prorataWethVaultCodeChunk25.drop 122 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 247) [0x5f, 0x5f, 0xfd]
    previewMintAssets_6522_compile (by rw [hlen]) (by decide) (revert_compile_at 7672)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7671 >>> 8).toUInt8, Nat.toUInt8 7671, 0x57] : Bytes) = (prorataWethVaultCodeChunk25.drop 118).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk29.drop 247).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk29.drop 248).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 67).take 51) ++ ((prorataWethVaultCodeChunk25.drop 118).take 4) = (prorataWethVaultCodeChunk25.drop 67).take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk25.drop 67) (i := 51) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 67).take 51), hj0]
  have hj1 : ((prorataWethVaultCodeChunk25.drop 67).take 55) ++ (prorataWethVaultCodeChunk25.drop 122) = prorataWethVaultCodeChunk25.drop 67 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 55 (prorataWethVaultCodeChunk25.drop 67)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 67).take 55), hj1]
  have hj2 : (prorataWethVaultCodeChunk29.take 247) ++ ((prorataWethVaultCodeChunk29.drop 247).take 1) = prorataWethVaultCodeChunk29.take 248 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 247) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk29.take 247), hj2]
  have hj3 : (prorataWethVaultCodeChunk29.take 248) ++ ((prorataWethVaultCodeChunk29.drop 248).take 3) = prorataWethVaultCodeChunk29.take 251 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 248) (j := 3)).symm
  rw [hj3]

private theorem previewMintReturnSize_6458_compile :
    Func.compile vaultTable 6458 (previewMintReturnSize) = some (prorataWethVaultCodeChunk25.drop 58 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 255) := by
  rw [previewMintReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk25.drop 58).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk25.drop 67 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 251) : Bytes).length = 1208 := by decide +kernel
  have hbranch := compile_branch vaultTable 6463 7675 _ _
    (prorataWethVaultCodeChunk25.drop 67 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 251) [0x5f, 0x5f, 0xfd]
    previewMintStage_6467_compile (by rw [hlen]) (by decide) (revert_compile_at 7676)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7675 >>> 8).toUInt8, Nat.toUInt8 7675, 0x57] : Bytes) = (prorataWethVaultCodeChunk25.drop 63).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk29.drop 251).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk29.drop 252).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 58).take 5) ++ ((prorataWethVaultCodeChunk25.drop 63).take 4) = (prorataWethVaultCodeChunk25.drop 58).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk25.drop 58) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 58).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk25.drop 58).take 9) ++ (prorataWethVaultCodeChunk25.drop 67) = prorataWethVaultCodeChunk25.drop 58 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk25.drop 58)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 58).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk29.take 251) ++ ((prorataWethVaultCodeChunk29.drop 251).take 1) = prorataWethVaultCodeChunk29.take 252 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 251) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk29.take 251), hj2]
  have hj3 : (prorataWethVaultCodeChunk29.take 252) ++ ((prorataWethVaultCodeChunk29.drop 252).take 3) = prorataWethVaultCodeChunk29.take 255 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk29) (i := 252) (j := 3)).symm
  rw [hj3]

private theorem previewMintRead_6430_compile :
    Func.compile vaultTable 6430 (previewMintRead) = some (prorataWethVaultCodeChunk25.drop 30 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 3) := by
  rw [previewMintRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk25.drop 30).take 24 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk25.drop 58 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 255) : Bytes).length = 1221 := by decide +kernel
  have hbranch := compile_branch vaultTable 6454 7679 _ _
    (prorataWethVaultCodeChunk25.drop 58 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29.take 255) [0x5f, 0x5f, 0xfd]
    previewMintReturnSize_6458_compile (by rw [hlen]) (by decide) (revert_compile_at 7680)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7679 >>> 8).toUInt8, Nat.toUInt8 7679, 0x57] : Bytes) = (prorataWethVaultCodeChunk25.drop 54).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = prorataWethVaultCodeChunk29.drop 255 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = prorataWethVaultCodeChunk30.take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 30).take 24) ++ ((prorataWethVaultCodeChunk25.drop 54).take 4) = (prorataWethVaultCodeChunk25.drop 30).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk25.drop 30) (i := 24) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 30).take 24), hj0]
  have hj1 : ((prorataWethVaultCodeChunk25.drop 30).take 28) ++ (prorataWethVaultCodeChunk25.drop 58) = prorataWethVaultCodeChunk25.drop 30 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 28 (prorataWethVaultCodeChunk25.drop 30)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 30).take 28), hj1]
  have hj2 : (prorataWethVaultCodeChunk29.take 255) ++ (prorataWethVaultCodeChunk29.drop 255) = prorataWethVaultCodeChunk29 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 255 (prorataWethVaultCodeChunk29)
  rw [← List.append_assoc (prorataWethVaultCodeChunk29.take 255), hj2]

private theorem previewMintStatic_6422_compile :
    Func.compile vaultTable 6422 (previewMintStatic) = some (prorataWethVaultCodeChunk25.drop 22 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7) := by
  rw [previewMintStatic, compile_prepend, maxDepositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk25.drop 22).take 4 := by
    rw [maxDepositStaticPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk25.drop 30 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 3) : Bytes).length = 1253 := by decide +kernel
  have hbranch := compile_branch vaultTable 6426 7683 _ _
    (prorataWethVaultCodeChunk25.drop 30 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 3) [0x5f, 0x5f, 0xfd]
    previewMintRead_6430_compile (by rw [hlen]) (by decide) (revert_compile_at 7684)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (7683 >>> 8).toUInt8, Nat.toUInt8 7683, 0x57] : Bytes) = (prorataWethVaultCodeChunk25.drop 26).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 3).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk30.drop 4).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 22).take 4) ++ ((prorataWethVaultCodeChunk25.drop 26).take 4) = (prorataWethVaultCodeChunk25.drop 22).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk25.drop 22) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 22).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk25.drop 22).take 8) ++ (prorataWethVaultCodeChunk25.drop 30) = prorataWethVaultCodeChunk25.drop 22 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk25.drop 22)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 22).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk30.take 3) ++ ((prorataWethVaultCodeChunk30.drop 3).take 1) = prorataWethVaultCodeChunk30.take 4 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30) (i := 3) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk30.take 3), hj2]
  have hj3 : (prorataWethVaultCodeChunk30.take 4) ++ ((prorataWethVaultCodeChunk30.drop 4).take 3) = prorataWethVaultCodeChunk30.take 7 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30) (i := 4) (j := 3)).symm
  rw [hj3]

private theorem previewMint_source_cut : ProrataWethVault.routed 1 ProrataWethVault.previewMint = nonpayable previewMintStatic := by rfl
private theorem previewMint_endpoint_compile :
    Func.compile vaultTable 6412 (ProrataWethVault.routed 1 ProrataWethVault.previewMint) = some (prorataWethVaultCodeChunk25.drop 12 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7) := by
  rw [previewMint_source_cut]
  have hcut : nonpayable previewMintStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert previewMintStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 6414 6421 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk25.drop 22 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7)
    (revert_compile_at 6418) (by rfl) (by decide) previewMintStatic_6422_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (6421 >>> 8).toUInt8, Nat.toUInt8 6421, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk25.drop 12).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (6421 >>> 8).toUInt8, Nat.toUInt8 6421, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk25.drop 12).take 10) ++ (prorataWethVaultCodeChunk25.drop 22) = prorataWethVaultCodeChunk25.drop 12 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk25.drop 12)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk25.drop 12).take 10), hj0]

private theorem finishQuotient_down_redeem_compile_at (n : Nat) :
    Func.compile vaultTable n (ProrataWethVault.finishQuotient .down ProrataWethVault.redeemAfterQuoteSlot) =
      some [0x61, 0x03, 0x00, 0x51, 0x61, 0x40, 0xaf, 0x56] := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, prepend]
  simp only [Func.compile, vault_table_redeemAfterQuote]
  rfl
private theorem redeemWideCore_down_compile_at (n : Nat) :
    Func.compile vaultTable n (ProrataWethVault.divideWideCore .down ProrataWethVault.redeemAfterQuoteSlot) =
      some (wideCorePrefix.flatMap Ninst.toBytes ++ ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes ++
        wideCoreSuffix.flatMap Ninst.toBytes ++ [0x61, 0x03, 0x00, 0x51, 0x61, 0x40, 0xaf, 0x56]) := by
  exact divideWideCore_compile_from_finish n .down ProrataWethVault.redeemAfterQuoteSlot _
    (finishQuotient_down_redeem_compile_at (n + 347))
private theorem redeemWide_source_cut :
    ProrataWethVault.divideWide .down ProrataWethVault.redeemAfterQuoteSlot =
      wideGuardPrefix +++ Func.branch Func.revert
        (ProrataWethVault.divideWideCore .down ProrataWethVault.redeemAfterQuoteSlot) := by rfl
private def redeemNonzero : Func := highZeroPrefix +++ Func.branch
  (ProrataWethVault.divideWide .down ProrataWethVault.redeemAfterQuoteSlot)
  (ProrataWethVault.divideSimple .down ProrataWethVault.redeemAfterQuoteSlot)
private theorem redeemDivide_source_cut :
    ProrataWethVault.divide512 .down ProrataWethVault.redeemAfterQuoteSlot =
      denominatorZeroPrefix +++ Func.branch redeemNonzero Func.revert := by rfl

private theorem redeemWideCore_4550_compile :
    Func.compile vaultTable 4550
      (ProrataWethVault.divideWideCore .down ProrataWethVault.redeemAfterQuoteSlot) =
      some (prorataWethVaultCodeChunk17.drop 198 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 41) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk17.drop 198 ++ prorataWethVaultCodeChunk18.take 59 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk18.drop 59).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = prorataWethVaultCodeChunk18.drop 150 ++ prorataWethVaultCodeChunk19.take 20 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk18.drop 150).take 63 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = prorataWethVaultCodeChunk18.drop 213 ++ prorataWethVaultCodeChunk19.take 20 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : ((prorataWethVaultCodeChunk18.drop 150).take 63) ++ (prorataWethVaultCodeChunk18.drop 213) = prorataWethVaultCodeChunk18.drop 150 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            List.take_append_drop 63 (prorataWethVaultCodeChunk18.drop 150)
        rw [← List.append_assoc ((prorataWethVaultCodeChunk18.drop 150).take 63), hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk19.drop 20).take 13 := by rfl
  have hfinish : ([0x61, 0x03, 0x00, 0x51, 0x61, 0x40, 0xaf, 0x56] : Bytes) = (prorataWethVaultCodeChunk19.drop 33).take 8 := by rfl
  rw [redeemWideCore_down_compile_at, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs, hfinish]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk18.take 59) ++ ((prorataWethVaultCodeChunk18.drop 59).take 91) = prorataWethVaultCodeChunk18.take 150 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk18) (i := 59) (j := 91)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk18.take 59), hj0]
  have hj1 : (prorataWethVaultCodeChunk18.take 150) ++ (prorataWethVaultCodeChunk18.drop 150) = prorataWethVaultCodeChunk18 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 150 (prorataWethVaultCodeChunk18)
  rw [← List.append_assoc (prorataWethVaultCodeChunk18.take 150), hj1]
  have hj2 : (prorataWethVaultCodeChunk19.take 20) ++ ((prorataWethVaultCodeChunk19.drop 20).take 13) = prorataWethVaultCodeChunk19.take 33 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19) (i := 20) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk19.take 20), hj2]
  have hj3 : (prorataWethVaultCodeChunk19.take 33) ++ ((prorataWethVaultCodeChunk19.drop 33).take 8) = prorataWethVaultCodeChunk19.take 41 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19) (i := 33) (j := 8)).symm
  rw [hj3]

private theorem redeemSimple_4906_compile :
    Func.compile vaultTable 4906 (ProrataWethVault.divideSimple .down ProrataWethVault.redeemAfterQuoteSlot) =
      some ((prorataWethVaultCodeChunk19.drop 42).take 34) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, prepend]
  simp only [Func.compile, vault_table_redeemAfterQuote]
  rfl

private theorem redeemWide_4533_compile :
    Func.compile vaultTable 4533 (ProrataWethVault.divideWide .down ProrataWethVault.redeemAfterQuoteSlot) = some (prorataWethVaultCodeChunk17.drop 181 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 41) := by
  rw [redeemWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk17.drop 181).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 4542 4549 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk17.drop 198 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 41)
    (revert_compile_at 4546) (by rw [hlen]) (by decide) redeemWideCore_4550_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4549 >>> 8).toUInt8, Nat.toUInt8 4549, 0x57] : Bytes) = (prorataWethVaultCodeChunk17.drop 190).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk17.drop 197).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk17.drop 194).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk17.drop 181).take 9) ++ ((prorataWethVaultCodeChunk17.drop 190).take 4) = (prorataWethVaultCodeChunk17.drop 181).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk17.drop 181) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 181).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk17.drop 181).take 13) ++ ((prorataWethVaultCodeChunk17.drop 194).take 3) = (prorataWethVaultCodeChunk17.drop 181).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk17.drop 181) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 181).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk17.drop 181).take 16) ++ ((prorataWethVaultCodeChunk17.drop 197).take 1) = (prorataWethVaultCodeChunk17.drop 181).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk17.drop 181) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 181).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk17.drop 181).take 17) ++ (prorataWethVaultCodeChunk17.drop 198) = prorataWethVaultCodeChunk17.drop 181 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk17.drop 181)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 181).take 17), hj3]

private theorem redeemNonzero_4524_compile :
    Func.compile vaultTable 4524 (redeemNonzero) = some (prorataWethVaultCodeChunk17.drop 172 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 76) := by
  rw [redeemNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk17.drop 172).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk17.drop 181 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 41) : Bytes).length = 372 := by decide +kernel
  have hbranch := compile_branch vaultTable 4529 4905 _ _
    (prorataWethVaultCodeChunk17.drop 181 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 41) ((prorataWethVaultCodeChunk19.drop 42).take 34)
    redeemWide_4533_compile (by rw [hlen]) (by decide) redeemSimple_4906_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4905 >>> 8).toUInt8, Nat.toUInt8 4905, 0x57] : Bytes) = (prorataWethVaultCodeChunk17.drop 177).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk19.drop 41).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk17.drop 172).take 5) ++ ((prorataWethVaultCodeChunk17.drop 177).take 4) = (prorataWethVaultCodeChunk17.drop 172).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk17.drop 172) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 172).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk17.drop 172).take 9) ++ (prorataWethVaultCodeChunk17.drop 181) = prorataWethVaultCodeChunk17.drop 172 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk17.drop 172)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 172).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk19.take 41) ++ ((prorataWethVaultCodeChunk19.drop 41).take 1) = prorataWethVaultCodeChunk19.take 42 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19) (i := 41) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk19.take 41), hj2]
  have hj3 : (prorataWethVaultCodeChunk19.take 42) ++ ((prorataWethVaultCodeChunk19.drop 42).take 34) = prorataWethVaultCodeChunk19.take 76 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19) (i := 42) (j := 34)).symm
  rw [hj3]

private theorem redeemDivide_4515_compile :
    Func.compile vaultTable 4515 (ProrataWethVault.divide512 .down ProrataWethVault.redeemAfterQuoteSlot) = some (prorataWethVaultCodeChunk17.drop 163 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 80) := by
  rw [redeemDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk17.drop 163).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk17.drop 172 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 76) : Bytes).length = 416 := by decide +kernel
  have hbranch := compile_branch vaultTable 4520 4940 _ _
    (prorataWethVaultCodeChunk17.drop 172 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 76) [0x5f, 0x5f, 0xfd]
    redeemNonzero_4524_compile (by rw [hlen]) (by decide) (revert_compile_at 4941)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4940 >>> 8).toUInt8, Nat.toUInt8 4940, 0x57] : Bytes) = (prorataWethVaultCodeChunk17.drop 168).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk19.drop 76).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk19.drop 77).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk17.drop 163).take 5) ++ ((prorataWethVaultCodeChunk17.drop 168).take 4) = (prorataWethVaultCodeChunk17.drop 163).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk17.drop 163) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 163).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk17.drop 163).take 9) ++ (prorataWethVaultCodeChunk17.drop 172) = prorataWethVaultCodeChunk17.drop 163 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk17.drop 163)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 163).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk19.take 76) ++ ((prorataWethVaultCodeChunk19.drop 76).take 1) = prorataWethVaultCodeChunk19.take 77 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19) (i := 76) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk19.take 76), hj2]
  have hj3 : (prorataWethVaultCodeChunk19.take 77) ++ ((prorataWethVaultCodeChunk19.drop 77).take 3) = prorataWethVaultCodeChunk19.take 80 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19) (i := 77) (j := 3)).symm
  rw [hj3]

private theorem redeemWideCore_5005_compile :
    Func.compile vaultTable 5005
      (ProrataWethVault.divideWideCore .down ProrataWethVault.redeemAfterQuoteSlot) =
      some (prorataWethVaultCodeChunk19.drop 141 ++ prorataWethVaultCodeChunk20.take 240) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk19.drop 141 ++ prorataWethVaultCodeChunk20.take 2 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk20.drop 2).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk20.drop 93).take 126 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk20.drop 93).take 63 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk20.drop 156).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : ((prorataWethVaultCodeChunk20.drop 93).take 63) ++ ((prorataWethVaultCodeChunk20.drop 156).take 63) = (prorataWethVaultCodeChunk20.drop 93).take 126 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk20.drop 93) (i := 63) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk20.drop 219).take 13 := by rfl
  have hfinish : ([0x61, 0x03, 0x00, 0x51, 0x61, 0x40, 0xaf, 0x56] : Bytes) = (prorataWethVaultCodeChunk20.drop 232).take 8 := by rfl
  rw [redeemWideCore_down_compile_at, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs, hfinish]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk20.take 2) ++ ((prorataWethVaultCodeChunk20.drop 2).take 91) = prorataWethVaultCodeChunk20.take 93 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk20) (i := 2) (j := 91)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk20.take 2), hj0]
  have hj1 : (prorataWethVaultCodeChunk20.take 93) ++ ((prorataWethVaultCodeChunk20.drop 93).take 126) = prorataWethVaultCodeChunk20.take 219 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk20) (i := 93) (j := 126)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk20.take 93), hj1]
  have hj2 : (prorataWethVaultCodeChunk20.take 219) ++ ((prorataWethVaultCodeChunk20.drop 219).take 13) = prorataWethVaultCodeChunk20.take 232 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk20) (i := 219) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk20.take 219), hj2]
  have hj3 : (prorataWethVaultCodeChunk20.take 232) ++ ((prorataWethVaultCodeChunk20.drop 232).take 8) = prorataWethVaultCodeChunk20.take 240 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk20) (i := 232) (j := 8)).symm
  rw [hj3]

private theorem redeemSimple_5361_compile :
    Func.compile vaultTable 5361 (ProrataWethVault.divideSimple .down ProrataWethVault.redeemAfterQuoteSlot) =
      some (prorataWethVaultCodeChunk20.drop 241 ++ prorataWethVaultCodeChunk21.take 19) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, prepend]
  simp only [Func.compile, vault_table_redeemAfterQuote]
  rfl

private theorem redeemWide_4988_compile :
    Func.compile vaultTable 4988 (ProrataWethVault.divideWide .down ProrataWethVault.redeemAfterQuoteSlot) = some (prorataWethVaultCodeChunk19.drop 124 ++ prorataWethVaultCodeChunk20.take 240) := by
  rw [redeemWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk19.drop 124).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 4997 5004 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk19.drop 141 ++ prorataWethVaultCodeChunk20.take 240)
    (revert_compile_at 5001) (by rw [hlen]) (by decide) redeemWideCore_5005_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5004 >>> 8).toUInt8, Nat.toUInt8 5004, 0x57] : Bytes) = (prorataWethVaultCodeChunk19.drop 133).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk19.drop 140).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk19.drop 137).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk19.drop 124).take 9) ++ ((prorataWethVaultCodeChunk19.drop 133).take 4) = (prorataWethVaultCodeChunk19.drop 124).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19.drop 124) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 124).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk19.drop 124).take 13) ++ ((prorataWethVaultCodeChunk19.drop 137).take 3) = (prorataWethVaultCodeChunk19.drop 124).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19.drop 124) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 124).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk19.drop 124).take 16) ++ ((prorataWethVaultCodeChunk19.drop 140).take 1) = (prorataWethVaultCodeChunk19.drop 124).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19.drop 124) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 124).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk19.drop 124).take 17) ++ (prorataWethVaultCodeChunk19.drop 141) = prorataWethVaultCodeChunk19.drop 124 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk19.drop 124)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 124).take 17), hj3]

private theorem redeemNonzero_4979_compile :
    Func.compile vaultTable 4979 (redeemNonzero) = some (prorataWethVaultCodeChunk19.drop 115 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 19) := by
  rw [redeemNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk19.drop 115).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk19.drop 124 ++ prorataWethVaultCodeChunk20.take 240) : Bytes).length = 372 := by decide +kernel
  have hbranch := compile_branch vaultTable 4984 5360 _ _
    (prorataWethVaultCodeChunk19.drop 124 ++ prorataWethVaultCodeChunk20.take 240) (prorataWethVaultCodeChunk20.drop 241 ++ prorataWethVaultCodeChunk21.take 19)
    redeemWide_4988_compile (by rw [hlen]) (by decide) redeemSimple_5361_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5360 >>> 8).toUInt8, Nat.toUInt8 5360, 0x57] : Bytes) = (prorataWethVaultCodeChunk19.drop 120).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk20.drop 240).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk19.drop 115).take 5) ++ ((prorataWethVaultCodeChunk19.drop 120).take 4) = (prorataWethVaultCodeChunk19.drop 115).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19.drop 115) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 115).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk19.drop 115).take 9) ++ (prorataWethVaultCodeChunk19.drop 124) = prorataWethVaultCodeChunk19.drop 115 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk19.drop 115)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 115).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk20.take 240) ++ ((prorataWethVaultCodeChunk20.drop 240).take 1) = prorataWethVaultCodeChunk20.take 241 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk20) (i := 240) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk20.take 240), hj2]
  have hj3 : (prorataWethVaultCodeChunk20.take 241) ++ (prorataWethVaultCodeChunk20.drop 241) = prorataWethVaultCodeChunk20 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 241 (prorataWethVaultCodeChunk20)
  rw [← List.append_assoc (prorataWethVaultCodeChunk20.take 241), hj3]

private theorem redeemDivide_4970_compile :
    Func.compile vaultTable 4970 (ProrataWethVault.divide512 .down ProrataWethVault.redeemAfterQuoteSlot) = some (prorataWethVaultCodeChunk19.drop 106 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 23) := by
  rw [redeemDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk19.drop 106).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk19.drop 115 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 19) : Bytes).length = 416 := by decide +kernel
  have hbranch := compile_branch vaultTable 4975 5395 _ _
    (prorataWethVaultCodeChunk19.drop 115 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 19) [0x5f, 0x5f, 0xfd]
    redeemNonzero_4979_compile (by rw [hlen]) (by decide) (revert_compile_at 5396)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5395 >>> 8).toUInt8, Nat.toUInt8 5395, 0x57] : Bytes) = (prorataWethVaultCodeChunk19.drop 111).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk21.drop 19).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk21.drop 20).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk19.drop 106).take 5) ++ ((prorataWethVaultCodeChunk19.drop 111).take 4) = (prorataWethVaultCodeChunk19.drop 106).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19.drop 106) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 106).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk19.drop 106).take 9) ++ (prorataWethVaultCodeChunk19.drop 115) = prorataWethVaultCodeChunk19.drop 106 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk19.drop 106)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 106).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk21.take 19) ++ ((prorataWethVaultCodeChunk21.drop 19).take 1) = prorataWethVaultCodeChunk21.take 20 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 19) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk21.take 19), hj2]
  have hj3 : (prorataWethVaultCodeChunk21.take 20) ++ ((prorataWethVaultCodeChunk21.drop 20).take 3) = prorataWethVaultCodeChunk21.take 23 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 20) (j := 3)).symm
  rw [hj3]

open ProrataWethVault Jaune.Ninst Ninst in
private def mutationAssetMulStage : Line := stagedDenominator ++ mstoreAt denominatorWord ++ loadWord amountWord ++ mstoreAt xWord ++ stagedAssetFactor ++ mstoreAt yWord ++ loadWord xWord ++ loadWord yWord ++ [mul] ++ mstoreAt lowWord
private theorem mutationAssetMulStage_size : prefixByteSize mutationAssetMulStage = 44 := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def mutationShiftStage : Line := loadWord amountWord ++ mstoreAt highWord ++ [pushB256 0] ++ mstoreAt lowWord ++ stagedDenominator ++ mstoreAt denominatorWord
private theorem mutationShiftStage_size : prefixByteSize mutationShiftStage = 25 := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def mutationArgs3Prefix : Line := arg 0 ++ mstoreAt amountWord ++ arg 1 ++ mstoreAt receiverWord ++ arg 2 ++ mstoreAt ownerWord
private theorem mutationArgs3Prefix_size : prefixByteSize mutationArgs3Prefix = 21 := by rfl

open ProrataWethVault in
private theorem redeemMul_source_cut :
    mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .down redeemAfterQuoteSlot =
      mutationAssetMulStage +++ maxDepositMulRecover +++ divide512 .down redeemAfterQuoteSlot := by rfl
open ProrataWethVault in
private theorem redeemShift_source_cut :
    shiftedDiv (loadWord amountWord) stagedDenominator .down redeemAfterQuoteSlot =
      mutationShiftStage +++ divide512 .down redeemAfterQuoteSlot := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def redeemArithmetic : Func := Func.branch (mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .down redeemAfterQuoteSlot) (shiftedDiv (loadWord amountWord) stagedDenominator .down redeemAfterQuoteSlot)

open ProrataWethVault Jaune.Ninst Ninst in
private def redeemAssets : Func := previewRedeemAssetsPrefix +++ redeemArithmetic

open ProrataWethVault Jaune.Ninst Ninst in
private def redeemStage : Func := previewRedeemStagePrefix +++ Func.branch redeemAssets Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def redeemReturnSize : Func := maxDepositReturnSizePrefix +++ Func.branch redeemStage Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def redeemRead : Func := maxDepositReadPrefix +++ Func.branch redeemReturnSize Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def redeemArgs : Func := mutationArgs3Prefix +++ redeemRead

open ProrataWethVault Jaune.Ninst Ninst in
private def redeemStatic : Func := transferStaticPrefix +++ Func.branch redeemArgs Func.revert

private theorem redeemMul_4386_compile :
    Func.compile vaultTable 4386 (ProrataWethVault.mulDiv (ProrataWethVault.loadWord ProrataWethVault.amountWord) ProrataWethVault.stagedAssetFactor ProrataWethVault.stagedDenominator .down ProrataWethVault.redeemAfterQuoteSlot) = some (prorataWethVaultCodeChunk17.drop 34 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 80) := by
  have hb0 : mutationAssetMulStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk17.drop 34).take 44 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk17.drop 78).take 85 := by
    rfl
  rw [redeemMul_source_cut]
  rw [compile_prepend, mutationAssetMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [redeemDivide_4515_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk17.drop 34).take 44) ++ ((prorataWethVaultCodeChunk17.drop 78).take 85) = (prorataWethVaultCodeChunk17.drop 34).take 129 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk17.drop 34) (i := 44) (j := 85)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 34).take 44), hj0]
  have hj1 : ((prorataWethVaultCodeChunk17.drop 34).take 129) ++ (prorataWethVaultCodeChunk17.drop 163) = prorataWethVaultCodeChunk17.drop 34 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 129 (prorataWethVaultCodeChunk17.drop 34)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 34).take 129), hj1]

private theorem redeemShift_4945_compile :
    Func.compile vaultTable 4945 (ProrataWethVault.shiftedDiv (ProrataWethVault.loadWord ProrataWethVault.amountWord) ProrataWethVault.stagedDenominator .down ProrataWethVault.redeemAfterQuoteSlot) = some (prorataWethVaultCodeChunk19.drop 81 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 23) := by
  have hb0 : mutationShiftStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk19.drop 81).take 25 := by
    rfl
  rw [redeemShift_source_cut]
  rw [compile_prepend, mutationShiftStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [redeemDivide_4970_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk19.drop 81).take 25) ++ (prorataWethVaultCodeChunk19.drop 106) = prorataWethVaultCodeChunk19.drop 81 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 25 (prorataWethVaultCodeChunk19.drop 81)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk19.drop 81).take 25), hj0]

private theorem redeemArithmetic_4382_compile :
    Func.compile vaultTable 4382 (redeemArithmetic) = some (prorataWethVaultCodeChunk17.drop 30 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 23) := by
  rw [redeemArithmetic]
  have hlen : ((prorataWethVaultCodeChunk17.drop 34 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 80) : Bytes).length = 558 := by decide +kernel
  have hbranch := compile_branch vaultTable 4382 4944 _ _
    (prorataWethVaultCodeChunk17.drop 34 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19.take 80) (prorataWethVaultCodeChunk19.drop 81 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 23)
    redeemMul_4386_compile (by rw [hlen]) (by decide) redeemShift_4945_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (4944 >>> 8).toUInt8, Nat.toUInt8 4944, 0x57] : Bytes) = (prorataWethVaultCodeChunk17.drop 30).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk19.drop 80).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk17.drop 30).take 4) ++ (prorataWethVaultCodeChunk17.drop 34) = prorataWethVaultCodeChunk17.drop 30 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk17.drop 30)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 30).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk19.take 80) ++ ((prorataWethVaultCodeChunk19.drop 80).take 1) = prorataWethVaultCodeChunk19.take 81 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk19) (i := 80) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk19.take 80), hj1]
  have hj2 : (prorataWethVaultCodeChunk19.take 81) ++ (prorataWethVaultCodeChunk19.drop 81) = prorataWethVaultCodeChunk19 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 81 (prorataWethVaultCodeChunk19)
  rw [← List.append_assoc (prorataWethVaultCodeChunk19.take 81), hj2]

private theorem redeemAssets_4376_compile :
    Func.compile vaultTable 4376 (redeemAssets) = some (prorataWethVaultCodeChunk17.drop 24 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 23) := by
  have hb0 : previewRedeemAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk17.drop 24).take 6 := by
    rw [previewRedeemAssetsPrefix_bytes]
    rfl
  rw [redeemAssets]
  rw [compile_prepend, previewRedeemAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [redeemArithmetic_4382_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk17.drop 24).take 6) ++ (prorataWethVaultCodeChunk17.drop 30) = prorataWethVaultCodeChunk17.drop 24 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 6 (prorataWethVaultCodeChunk17.drop 24)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk17.drop 24).take 6), hj0]

private theorem redeemStage_4321_compile :
    Func.compile vaultTable 4321 (redeemStage) = some (prorataWethVaultCodeChunk16.drop 225 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 27) := by
  rw [redeemStage, compile_prepend, previewRedeemStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : previewRedeemStagePrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk16.drop 225 ++ prorataWethVaultCodeChunk17.take 20 := by
    rw [previewRedeemStagePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk17.drop 24 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 23) : Bytes).length = 1023 := by decide +kernel
  have hbranch := compile_branch vaultTable 4372 5399 _ _
    (prorataWethVaultCodeChunk17.drop 24 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 23) [0x5f, 0x5f, 0xfd]
    redeemAssets_4376_compile (by rw [hlen]) (by decide) (revert_compile_at 5400)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5399 >>> 8).toUInt8, Nat.toUInt8 5399, 0x57] : Bytes) = (prorataWethVaultCodeChunk17.drop 20).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk21.drop 23).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk21.drop 24).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk17.take 20) ++ ((prorataWethVaultCodeChunk17.drop 20).take 4) = prorataWethVaultCodeChunk17.take 24 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk17) (i := 20) (j := 4)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk17.take 20), hj0]
  have hj1 : (prorataWethVaultCodeChunk17.take 24) ++ (prorataWethVaultCodeChunk17.drop 24) = prorataWethVaultCodeChunk17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 24 (prorataWethVaultCodeChunk17)
  rw [← List.append_assoc (prorataWethVaultCodeChunk17.take 24), hj1]
  have hj2 : (prorataWethVaultCodeChunk21.take 23) ++ ((prorataWethVaultCodeChunk21.drop 23).take 1) = prorataWethVaultCodeChunk21.take 24 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 23) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk21.take 23), hj2]
  have hj3 : (prorataWethVaultCodeChunk21.take 24) ++ ((prorataWethVaultCodeChunk21.drop 24).take 3) = prorataWethVaultCodeChunk21.take 27 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 24) (j := 3)).symm
  rw [hj3]

private theorem redeemReturnSize_4312_compile :
    Func.compile vaultTable 4312 (redeemReturnSize) = some (prorataWethVaultCodeChunk16.drop 216 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 31) := by
  rw [redeemReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk16.drop 216).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk16.drop 225 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 27) : Bytes).length = 1082 := by decide +kernel
  have hbranch := compile_branch vaultTable 4317 5403 _ _
    (prorataWethVaultCodeChunk16.drop 225 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 27) [0x5f, 0x5f, 0xfd]
    redeemStage_4321_compile (by rw [hlen]) (by decide) (revert_compile_at 5404)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5403 >>> 8).toUInt8, Nat.toUInt8 5403, 0x57] : Bytes) = (prorataWethVaultCodeChunk16.drop 221).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk21.drop 27).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk21.drop 28).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 216).take 5) ++ ((prorataWethVaultCodeChunk16.drop 221).take 4) = (prorataWethVaultCodeChunk16.drop 216).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16.drop 216) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 216).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk16.drop 216).take 9) ++ (prorataWethVaultCodeChunk16.drop 225) = prorataWethVaultCodeChunk16.drop 216 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk16.drop 216)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 216).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk21.take 27) ++ ((prorataWethVaultCodeChunk21.drop 27).take 1) = prorataWethVaultCodeChunk21.take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 27) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk21.take 27), hj2]
  have hj3 : (prorataWethVaultCodeChunk21.take 28) ++ ((prorataWethVaultCodeChunk21.drop 28).take 3) = prorataWethVaultCodeChunk21.take 31 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 28) (j := 3)).symm
  rw [hj3]

private theorem redeemRead_4284_compile :
    Func.compile vaultTable 4284 (redeemRead) = some (prorataWethVaultCodeChunk16.drop 188 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 35) := by
  rw [redeemRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk16.drop 188).take 24 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk16.drop 216 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 31) : Bytes).length = 1095 := by decide +kernel
  have hbranch := compile_branch vaultTable 4308 5407 _ _
    (prorataWethVaultCodeChunk16.drop 216 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 31) [0x5f, 0x5f, 0xfd]
    redeemReturnSize_4312_compile (by rw [hlen]) (by decide) (revert_compile_at 5408)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5407 >>> 8).toUInt8, Nat.toUInt8 5407, 0x57] : Bytes) = (prorataWethVaultCodeChunk16.drop 212).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk21.drop 31).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk21.drop 32).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 188).take 24) ++ ((prorataWethVaultCodeChunk16.drop 212).take 4) = (prorataWethVaultCodeChunk16.drop 188).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16.drop 188) (i := 24) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 188).take 24), hj0]
  have hj1 : ((prorataWethVaultCodeChunk16.drop 188).take 28) ++ (prorataWethVaultCodeChunk16.drop 216) = prorataWethVaultCodeChunk16.drop 188 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 28 (prorataWethVaultCodeChunk16.drop 188)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 188).take 28), hj1]
  have hj2 : (prorataWethVaultCodeChunk21.take 31) ++ ((prorataWethVaultCodeChunk21.drop 31).take 1) = prorataWethVaultCodeChunk21.take 32 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 31) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk21.take 31), hj2]
  have hj3 : (prorataWethVaultCodeChunk21.take 32) ++ ((prorataWethVaultCodeChunk21.drop 32).take 3) = prorataWethVaultCodeChunk21.take 35 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 32) (j := 3)).symm
  rw [hj3]

private theorem redeemArgs_4263_compile :
    Func.compile vaultTable 4263 (redeemArgs) = some (prorataWethVaultCodeChunk16.drop 167 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 35) := by
  have hb0 : mutationArgs3Prefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk16.drop 167).take 21 := by
    rfl
  rw [redeemArgs]
  rw [compile_prepend, mutationArgs3Prefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [redeemRead_4284_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 167).take 21) ++ (prorataWethVaultCodeChunk16.drop 188) = prorataWethVaultCodeChunk16.drop 167 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 21 (prorataWethVaultCodeChunk16.drop 167)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 167).take 21), hj0]

private theorem redeemStatic_4255_compile :
    Func.compile vaultTable 4255 (redeemStatic) = some (prorataWethVaultCodeChunk16.drop 159 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 39) := by
  rw [redeemStatic, compile_prepend, transferStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : transferStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk16.drop 159).take 4 := by
    rfl
  have hlen : ((prorataWethVaultCodeChunk16.drop 167 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 35) : Bytes).length = 1148 := by decide +kernel
  have hbranch := compile_branch vaultTable 4259 5411 _ _
    (prorataWethVaultCodeChunk16.drop 167 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 35) [0x5f, 0x5f, 0xfd]
    redeemArgs_4263_compile (by rw [hlen]) (by decide) (revert_compile_at 5412)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5411 >>> 8).toUInt8, Nat.toUInt8 5411, 0x57] : Bytes) = (prorataWethVaultCodeChunk16.drop 163).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk21.drop 35).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk21.drop 36).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 159).take 4) ++ ((prorataWethVaultCodeChunk16.drop 163).take 4) = (prorataWethVaultCodeChunk16.drop 159).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16.drop 159) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 159).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk16.drop 159).take 8) ++ (prorataWethVaultCodeChunk16.drop 167) = prorataWethVaultCodeChunk16.drop 159 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk16.drop 159)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 159).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk21.take 35) ++ ((prorataWethVaultCodeChunk21.drop 35).take 1) = prorataWethVaultCodeChunk21.take 36 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 35) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk21.take 35), hj2]
  have hj3 : (prorataWethVaultCodeChunk21.take 36) ++ ((prorataWethVaultCodeChunk21.drop 36).take 3) = prorataWethVaultCodeChunk21.take 39 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 36) (j := 3)).symm
  rw [hj3]

private theorem redeem_source_cut : ProrataWethVault.routed 3 ProrataWethVault.redeem = nonpayable redeemStatic := by rfl
private theorem redeem_endpoint_compile :
    Func.compile vaultTable 4245 (ProrataWethVault.routed 3 ProrataWethVault.redeem) = some (prorataWethVaultCodeChunk16.drop 149 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 39) := by
  rw [redeem_source_cut]
  have hcut : nonpayable redeemStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert redeemStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 4247 4254 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk16.drop 159 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 39)
    (revert_compile_at 4251) (by rfl) (by decide) redeemStatic_4255_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (4254 >>> 8).toUInt8, Nat.toUInt8 4254, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk16.drop 149).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (4254 >>> 8).toUInt8, Nat.toUInt8 4254, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 149).take 10) ++ (prorataWethVaultCodeChunk16.drop 159) = prorataWethVaultCodeChunk16.drop 149 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk16.drop 149)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 149).take 10), hj0]

private theorem mintWide_source_cut :
    ProrataWethVault.divideWide .up ProrataWethVault.mintAfterQuoteSlot =
      wideGuardPrefix +++ Func.branch Func.revert
        (ProrataWethVault.divideWideCore .up ProrataWethVault.mintAfterQuoteSlot) := by rfl
private def mintNonzero : Func := highZeroPrefix +++ Func.branch
  (ProrataWethVault.divideWide .up ProrataWethVault.mintAfterQuoteSlot)
  (ProrataWethVault.divideSimple .up ProrataWethVault.mintAfterQuoteSlot)
private theorem mintDivide_source_cut :
    ProrataWethVault.divide512 .up ProrataWethVault.mintAfterQuoteSlot =
      denominatorZeroPrefix +++ Func.branch mintNonzero Func.revert := by rfl

private theorem mintFinish_8532_compile :
    Func.compile vaultTable 8532 (ProrataWethVault.finishQuotient .up ProrataWethVault.mintAfterQuoteSlot) =
      some ((prorataWethVaultCodeChunk33.drop 84).take 40) := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, isMax, prepend]
  simp only [Func.compile, vault_table_mintAfterQuote]
  rfl

private theorem mintWideCore_8185_compile :
    Func.compile vaultTable 8185 (ProrataWethVault.divideWideCore .up ProrataWethVault.mintAfterQuoteSlot) =
      some (prorataWethVaultCodeChunk31.drop 249 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 124) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk31.drop 249 ++ prorataWethVaultCodeChunk32.take 110 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk32.drop 110).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = prorataWethVaultCodeChunk32.drop 201 ++ prorataWethVaultCodeChunk33.take 71 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = prorataWethVaultCodeChunk32.drop 201 ++ prorataWethVaultCodeChunk33.take 8 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk33.drop 8).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : (prorataWethVaultCodeChunk33.take 8) ++ ((prorataWethVaultCodeChunk33.drop 8).take 63) = prorataWethVaultCodeChunk33.take 71 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk33) (i := 8) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk33.drop 71).take 13 := by rfl
  have hcomp := divideWideCore_compile_from_finish 8185 .up ProrataWethVault.mintAfterQuoteSlot
    ((prorataWethVaultCodeChunk33.drop 84).take 40) mintFinish_8532_compile
  rw [hcomp, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk32.take 110) ++ ((prorataWethVaultCodeChunk32.drop 110).take 91) = prorataWethVaultCodeChunk32.take 201 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk32) (i := 110) (j := 91)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk32.take 110), hj0]
  have hj1 : (prorataWethVaultCodeChunk32.take 201) ++ (prorataWethVaultCodeChunk32.drop 201) = prorataWethVaultCodeChunk32 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 201 (prorataWethVaultCodeChunk32)
  rw [← List.append_assoc (prorataWethVaultCodeChunk32.take 201), hj1]
  have hj2 : (prorataWethVaultCodeChunk33.take 71) ++ ((prorataWethVaultCodeChunk33.drop 71).take 13) = prorataWethVaultCodeChunk33.take 84 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33) (i := 71) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk33.take 71), hj2]
  have hj3 : (prorataWethVaultCodeChunk33.take 84) ++ ((prorataWethVaultCodeChunk33.drop 84).take 40) = prorataWethVaultCodeChunk33.take 124 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33) (i := 84) (j := 40)).symm
  rw [hj3]

private theorem mintSimple_8573_compile :
    Func.compile vaultTable 8573 (ProrataWethVault.divideSimple .up ProrataWethVault.mintAfterQuoteSlot) =
      some ((prorataWethVaultCodeChunk33.drop 125).take 66) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, isMax, prepend]
  simp only [Func.compile, vault_table_mintAfterQuote]
  rfl

private theorem mintWide_8168_compile :
    Func.compile vaultTable 8168 (ProrataWethVault.divideWide .up ProrataWethVault.mintAfterQuoteSlot) = some (prorataWethVaultCodeChunk31.drop 232 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 124) := by
  rw [mintWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 232).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 8177 8184 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk31.drop 249 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 124)
    (revert_compile_at 8181) (by rw [hlen]) (by decide) mintWideCore_8185_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (8184 >>> 8).toUInt8, Nat.toUInt8 8184, 0x57] : Bytes) = (prorataWethVaultCodeChunk31.drop 241).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk31.drop 248).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk31.drop 245).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 232).take 9) ++ ((prorataWethVaultCodeChunk31.drop 241).take 4) = (prorataWethVaultCodeChunk31.drop 232).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 232) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 232).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk31.drop 232).take 13) ++ ((prorataWethVaultCodeChunk31.drop 245).take 3) = (prorataWethVaultCodeChunk31.drop 232).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 232) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 232).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk31.drop 232).take 16) ++ ((prorataWethVaultCodeChunk31.drop 248).take 1) = (prorataWethVaultCodeChunk31.drop 232).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 232) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 232).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk31.drop 232).take 17) ++ (prorataWethVaultCodeChunk31.drop 249) = prorataWethVaultCodeChunk31.drop 232 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk31.drop 232)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 232).take 17), hj3]

private theorem mintNonzero_8159_compile :
    Func.compile vaultTable 8159 (mintNonzero) = some (prorataWethVaultCodeChunk31.drop 223 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 191) := by
  rw [mintNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 223).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk31.drop 232 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 124) : Bytes).length = 404 := by decide +kernel
  have hbranch := compile_branch vaultTable 8164 8572 _ _
    (prorataWethVaultCodeChunk31.drop 232 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 124) ((prorataWethVaultCodeChunk33.drop 125).take 66)
    mintWide_8168_compile (by rw [hlen]) (by decide) mintSimple_8573_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (8572 >>> 8).toUInt8, Nat.toUInt8 8572, 0x57] : Bytes) = (prorataWethVaultCodeChunk31.drop 228).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk33.drop 124).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 223).take 5) ++ ((prorataWethVaultCodeChunk31.drop 228).take 4) = (prorataWethVaultCodeChunk31.drop 223).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 223) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 223).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk31.drop 223).take 9) ++ (prorataWethVaultCodeChunk31.drop 232) = prorataWethVaultCodeChunk31.drop 223 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk31.drop 223)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 223).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk33.take 124) ++ ((prorataWethVaultCodeChunk33.drop 124).take 1) = prorataWethVaultCodeChunk33.take 125 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33) (i := 124) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk33.take 124), hj2]
  have hj3 : (prorataWethVaultCodeChunk33.take 125) ++ ((prorataWethVaultCodeChunk33.drop 125).take 66) = prorataWethVaultCodeChunk33.take 191 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33) (i := 125) (j := 66)).symm
  rw [hj3]

private theorem mintDivide_8150_compile :
    Func.compile vaultTable 8150 (ProrataWethVault.divide512 .up ProrataWethVault.mintAfterQuoteSlot) = some (prorataWethVaultCodeChunk31.drop 214 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 195) := by
  rw [mintDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 214).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk31.drop 223 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 191) : Bytes).length = 480 := by decide +kernel
  have hbranch := compile_branch vaultTable 8155 8639 _ _
    (prorataWethVaultCodeChunk31.drop 223 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 191) [0x5f, 0x5f, 0xfd]
    mintNonzero_8159_compile (by rw [hlen]) (by decide) (revert_compile_at 8640)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (8639 >>> 8).toUInt8, Nat.toUInt8 8639, 0x57] : Bytes) = (prorataWethVaultCodeChunk31.drop 219).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk33.drop 191).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk33.drop 192).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 214).take 5) ++ ((prorataWethVaultCodeChunk31.drop 219).take 4) = (prorataWethVaultCodeChunk31.drop 214).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 214) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 214).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk31.drop 214).take 9) ++ (prorataWethVaultCodeChunk31.drop 223) = prorataWethVaultCodeChunk31.drop 214 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk31.drop 214)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 214).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk33.take 191) ++ ((prorataWethVaultCodeChunk33.drop 191).take 1) = prorataWethVaultCodeChunk33.take 192 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33) (i := 191) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk33.take 191), hj2]
  have hj3 : (prorataWethVaultCodeChunk33.take 192) ++ ((prorataWethVaultCodeChunk33.drop 192).take 3) = prorataWethVaultCodeChunk33.take 195 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33) (i := 192) (j := 3)).symm
  rw [hj3]

private theorem mintFinish_9051_compile :
    Func.compile vaultTable 9051 (ProrataWethVault.finishQuotient .up ProrataWethVault.mintAfterQuoteSlot) =
      some ((prorataWethVaultCodeChunk35.drop 91).take 40) := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, isMax, prepend]
  simp only [Func.compile, vault_table_mintAfterQuote]
  rfl

private theorem mintWideCore_8704_compile :
    Func.compile vaultTable 8704 (ProrataWethVault.divideWideCore .up ProrataWethVault.mintAfterQuoteSlot) =
      some (prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 131) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk34.take 117 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk34.drop 117).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = prorataWethVaultCodeChunk34.drop 208 ++ prorataWethVaultCodeChunk35.take 78 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = prorataWethVaultCodeChunk34.drop 208 ++ prorataWethVaultCodeChunk35.take 15 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk35.drop 15).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : (prorataWethVaultCodeChunk35.take 15) ++ ((prorataWethVaultCodeChunk35.drop 15).take 63) = prorataWethVaultCodeChunk35.take 78 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk35) (i := 15) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk35.drop 78).take 13 := by rfl
  have hcomp := divideWideCore_compile_from_finish 8704 .up ProrataWethVault.mintAfterQuoteSlot
    ((prorataWethVaultCodeChunk35.drop 91).take 40) mintFinish_9051_compile
  rw [hcomp, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk34.take 117) ++ ((prorataWethVaultCodeChunk34.drop 117).take 91) = prorataWethVaultCodeChunk34.take 208 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk34) (i := 117) (j := 91)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk34.take 117), hj0]
  have hj1 : (prorataWethVaultCodeChunk34.take 208) ++ (prorataWethVaultCodeChunk34.drop 208) = prorataWethVaultCodeChunk34 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 208 (prorataWethVaultCodeChunk34)
  rw [← List.append_assoc (prorataWethVaultCodeChunk34.take 208), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 78) ++ ((prorataWethVaultCodeChunk35.drop 78).take 13) = prorataWethVaultCodeChunk35.take 91 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 78) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 78), hj2]
  have hj3 : (prorataWethVaultCodeChunk35.take 91) ++ ((prorataWethVaultCodeChunk35.drop 91).take 40) = prorataWethVaultCodeChunk35.take 131 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 91) (j := 40)).symm
  rw [hj3]

private theorem mintSimple_9092_compile :
    Func.compile vaultTable 9092 (ProrataWethVault.divideSimple .up ProrataWethVault.mintAfterQuoteSlot) =
      some ((prorataWethVaultCodeChunk35.drop 132).take 66) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, isMax, prepend]
  simp only [Func.compile, vault_table_mintAfterQuote]
  rfl

private theorem mintWide_8687_compile :
    Func.compile vaultTable 8687 (ProrataWethVault.divideWide .up ProrataWethVault.mintAfterQuoteSlot) = some (prorataWethVaultCodeChunk33.drop 239 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 131) := by
  rw [mintWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk33.drop 239).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 8696 8703 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 131)
    (revert_compile_at 8700) (by rw [hlen]) (by decide) mintWideCore_8704_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (8703 >>> 8).toUInt8, Nat.toUInt8 8703, 0x57] : Bytes) = (prorataWethVaultCodeChunk33.drop 248).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = prorataWethVaultCodeChunk33.drop 255 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk33.drop 252).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk33.drop 239).take 9) ++ ((prorataWethVaultCodeChunk33.drop 248).take 4) = (prorataWethVaultCodeChunk33.drop 239).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33.drop 239) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 239).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk33.drop 239).take 13) ++ ((prorataWethVaultCodeChunk33.drop 252).take 3) = (prorataWethVaultCodeChunk33.drop 239).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33.drop 239) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 239).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk33.drop 239).take 16) ++ (prorataWethVaultCodeChunk33.drop 255) = prorataWethVaultCodeChunk33.drop 239 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 16 (prorataWethVaultCodeChunk33.drop 239)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 239).take 16), hj2]

private theorem mintNonzero_8678_compile :
    Func.compile vaultTable 8678 (mintNonzero) = some (prorataWethVaultCodeChunk33.drop 230 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 198) := by
  rw [mintNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk33.drop 230).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk33.drop 239 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 131) : Bytes).length = 404 := by decide +kernel
  have hbranch := compile_branch vaultTable 8683 9091 _ _
    (prorataWethVaultCodeChunk33.drop 239 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 131) ((prorataWethVaultCodeChunk35.drop 132).take 66)
    mintWide_8687_compile (by rw [hlen]) (by decide) mintSimple_9092_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (9091 >>> 8).toUInt8, Nat.toUInt8 9091, 0x57] : Bytes) = (prorataWethVaultCodeChunk33.drop 235).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk35.drop 131).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk33.drop 230).take 5) ++ ((prorataWethVaultCodeChunk33.drop 235).take 4) = (prorataWethVaultCodeChunk33.drop 230).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33.drop 230) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 230).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk33.drop 230).take 9) ++ (prorataWethVaultCodeChunk33.drop 239) = prorataWethVaultCodeChunk33.drop 230 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk33.drop 230)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 230).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 131) ++ ((prorataWethVaultCodeChunk35.drop 131).take 1) = prorataWethVaultCodeChunk35.take 132 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 131) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 131), hj2]
  have hj3 : (prorataWethVaultCodeChunk35.take 132) ++ ((prorataWethVaultCodeChunk35.drop 132).take 66) = prorataWethVaultCodeChunk35.take 198 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 132) (j := 66)).symm
  rw [hj3]

private theorem mintDivide_8669_compile :
    Func.compile vaultTable 8669 (ProrataWethVault.divide512 .up ProrataWethVault.mintAfterQuoteSlot) = some (prorataWethVaultCodeChunk33.drop 221 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 202) := by
  rw [mintDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk33.drop 221).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk33.drop 230 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 198) : Bytes).length = 480 := by decide +kernel
  have hbranch := compile_branch vaultTable 8674 9158 _ _
    (prorataWethVaultCodeChunk33.drop 230 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 198) [0x5f, 0x5f, 0xfd]
    mintNonzero_8678_compile (by rw [hlen]) (by decide) (revert_compile_at 9159)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (9158 >>> 8).toUInt8, Nat.toUInt8 9158, 0x57] : Bytes) = (prorataWethVaultCodeChunk33.drop 226).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk35.drop 198).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk35.drop 199).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk33.drop 221).take 5) ++ ((prorataWethVaultCodeChunk33.drop 226).take 4) = (prorataWethVaultCodeChunk33.drop 221).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33.drop 221) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 221).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk33.drop 221).take 9) ++ (prorataWethVaultCodeChunk33.drop 230) = prorataWethVaultCodeChunk33.drop 221 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk33.drop 221)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 221).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 198) ++ ((prorataWethVaultCodeChunk35.drop 198).take 1) = prorataWethVaultCodeChunk35.take 199 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 198) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 198), hj2]
  have hj3 : (prorataWethVaultCodeChunk35.take 199) ++ ((prorataWethVaultCodeChunk35.drop 199).take 3) = prorataWethVaultCodeChunk35.take 202 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 199) (j := 3)).symm
  rw [hj3]

open ProrataWethVault in
private theorem mintShift_source_cut : shiftedDiv (loadWord amountWord) stagedDenominator .up mintAfterQuoteSlot =
    mutationShiftStage +++ divide512 .up mintAfterQuoteSlot := by rfl

open ProrataWethVault in
private theorem mintMul_source_cut : mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .up mintAfterQuoteSlot =
    mutationAssetMulStage +++ maxDepositMulRecover +++ divide512 .up mintAfterQuoteSlot := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def mintArithmetic : Func := Func.branch (mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .up mintAfterQuoteSlot) (shiftedDiv (loadWord amountWord) stagedDenominator .up mintAfterQuoteSlot)

open ProrataWethVault Jaune.Ninst Ninst in
private def mintAssets : Func := previewRedeemAssetsPrefix +++ mintArithmetic

open ProrataWethVault Jaune.Ninst Ninst in
private def mintStage : Func := previewRedeemStagePrefix +++ Func.branch mintAssets Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def mintReturnSize : Func := maxDepositReturnSizePrefix +++ Func.branch mintStage Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def mintRead : Func := maxDepositReadPrefix +++ Func.branch mintReturnSize Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def mintArgs : Func := depositArgsPrefix +++ mintRead

open ProrataWethVault Jaune.Ninst Ninst in
private def mintStatic : Func := depositStaticPrefix +++ Func.branch mintArgs Func.revert

open ProrataWethVault in
private theorem mintMul_8021_compile :
    Func.compile vaultTable 8021 (mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .up mintAfterQuoteSlot) = some (prorataWethVaultCodeChunk31.drop 85 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 195) := by
  have hb0 : mutationAssetMulStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 85).take 44 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 129).take 85 := by
    rfl
  rw [mintMul_source_cut]
  rw [compile_prepend, mutationAssetMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [mintDivide_8150_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 85).take 44) ++ ((prorataWethVaultCodeChunk31.drop 129).take 85) = (prorataWethVaultCodeChunk31.drop 85).take 129 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 85) (i := 44) (j := 85)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 85).take 44), hj0]
  have hj1 : ((prorataWethVaultCodeChunk31.drop 85).take 129) ++ (prorataWethVaultCodeChunk31.drop 214) = prorataWethVaultCodeChunk31.drop 85 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 129 (prorataWethVaultCodeChunk31.drop 85)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 85).take 129), hj1]

open ProrataWethVault in
private theorem mintShift_8644_compile :
    Func.compile vaultTable 8644 (shiftedDiv (loadWord amountWord) stagedDenominator .up mintAfterQuoteSlot) = some (prorataWethVaultCodeChunk33.drop 196 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 202) := by
  have hb0 : mutationShiftStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk33.drop 196).take 25 := by
    rfl
  rw [mintShift_source_cut]
  rw [compile_prepend, mutationShiftStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [mintDivide_8669_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk33.drop 196).take 25) ++ (prorataWethVaultCodeChunk33.drop 221) = prorataWethVaultCodeChunk33.drop 196 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 25 (prorataWethVaultCodeChunk33.drop 196)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk33.drop 196).take 25), hj0]

private theorem mintArithmetic_8017_compile :
    Func.compile vaultTable 8017 (mintArithmetic) = some (prorataWethVaultCodeChunk31.drop 81 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 202) := by
  rw [mintArithmetic]
  have hlen : ((prorataWethVaultCodeChunk31.drop 85 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 195) : Bytes).length = 622 := by decide +kernel
  have hbranch := compile_branch vaultTable 8017 8643 _ _
    (prorataWethVaultCodeChunk31.drop 85 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33.take 195) (prorataWethVaultCodeChunk33.drop 196 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 202)
    mintMul_8021_compile (by rw [hlen]) (by decide) mintShift_8644_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (8643 >>> 8).toUInt8, Nat.toUInt8 8643, 0x57] : Bytes) = (prorataWethVaultCodeChunk31.drop 81).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk33.drop 195).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 81).take 4) ++ (prorataWethVaultCodeChunk31.drop 85) = prorataWethVaultCodeChunk31.drop 81 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk31.drop 81)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 81).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk33.take 195) ++ ((prorataWethVaultCodeChunk33.drop 195).take 1) = prorataWethVaultCodeChunk33.take 196 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk33) (i := 195) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk33.take 195), hj1]
  have hj2 : (prorataWethVaultCodeChunk33.take 196) ++ (prorataWethVaultCodeChunk33.drop 196) = prorataWethVaultCodeChunk33 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 196 (prorataWethVaultCodeChunk33)
  rw [← List.append_assoc (prorataWethVaultCodeChunk33.take 196), hj2]

private theorem mintAssets_8011_compile :
    Func.compile vaultTable 8011 (mintAssets) = some (prorataWethVaultCodeChunk31.drop 75 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 202) := by
  have hb0 : previewRedeemAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 75).take 6 := by
    rw [previewRedeemAssetsPrefix_bytes]
    rfl
  rw [mintAssets]
  rw [compile_prepend, previewRedeemAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [mintArithmetic_8017_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 75).take 6) ++ (prorataWethVaultCodeChunk31.drop 81) = prorataWethVaultCodeChunk31.drop 75 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 6 (prorataWethVaultCodeChunk31.drop 75)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 75).take 6), hj0]

private theorem mintStage_7956_compile :
    Func.compile vaultTable 7956 (mintStage) = some (prorataWethVaultCodeChunk31.drop 20 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 206) := by
  rw [mintStage, compile_prepend, previewRedeemStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : previewRedeemStagePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 20).take 51 := by
    rw [previewRedeemStagePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk31.drop 75 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 202) : Bytes).length = 1151 := by decide +kernel
  have hbranch := compile_branch vaultTable 8007 9162 _ _
    (prorataWethVaultCodeChunk31.drop 75 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 202) [0x5f, 0x5f, 0xfd]
    mintAssets_8011_compile (by rw [hlen]) (by decide) (revert_compile_at 9163)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (9162 >>> 8).toUInt8, Nat.toUInt8 9162, 0x57] : Bytes) = (prorataWethVaultCodeChunk31.drop 71).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk35.drop 202).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk35.drop 203).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 20).take 51) ++ ((prorataWethVaultCodeChunk31.drop 71).take 4) = (prorataWethVaultCodeChunk31.drop 20).take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 20) (i := 51) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 20).take 51), hj0]
  have hj1 : ((prorataWethVaultCodeChunk31.drop 20).take 55) ++ (prorataWethVaultCodeChunk31.drop 75) = prorataWethVaultCodeChunk31.drop 20 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 55 (prorataWethVaultCodeChunk31.drop 20)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 20).take 55), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 202) ++ ((prorataWethVaultCodeChunk35.drop 202).take 1) = prorataWethVaultCodeChunk35.take 203 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 202) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 202), hj2]
  have hj3 : (prorataWethVaultCodeChunk35.take 203) ++ ((prorataWethVaultCodeChunk35.drop 203).take 3) = prorataWethVaultCodeChunk35.take 206 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 203) (j := 3)).symm
  rw [hj3]

private theorem mintReturnSize_7947_compile :
    Func.compile vaultTable 7947 (mintReturnSize) = some (prorataWethVaultCodeChunk31.drop 11 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 210) := by
  rw [mintReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk31.drop 11).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk31.drop 20 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 206) : Bytes).length = 1210 := by decide +kernel
  have hbranch := compile_branch vaultTable 7952 9166 _ _
    (prorataWethVaultCodeChunk31.drop 20 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 206) [0x5f, 0x5f, 0xfd]
    mintStage_7956_compile (by rw [hlen]) (by decide) (revert_compile_at 9167)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (9166 >>> 8).toUInt8, Nat.toUInt8 9166, 0x57] : Bytes) = (prorataWethVaultCodeChunk31.drop 16).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk35.drop 206).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk35.drop 207).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk31.drop 11).take 5) ++ ((prorataWethVaultCodeChunk31.drop 16).take 4) = (prorataWethVaultCodeChunk31.drop 11).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31.drop 11) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 11).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk31.drop 11).take 9) ++ (prorataWethVaultCodeChunk31.drop 20) = prorataWethVaultCodeChunk31.drop 11 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk31.drop 11)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk31.drop 11).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 206) ++ ((prorataWethVaultCodeChunk35.drop 206).take 1) = prorataWethVaultCodeChunk35.take 207 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 206) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 206), hj2]
  have hj3 : (prorataWethVaultCodeChunk35.take 207) ++ ((prorataWethVaultCodeChunk35.drop 207).take 3) = prorataWethVaultCodeChunk35.take 210 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 207) (j := 3)).symm
  rw [hj3]

private theorem mintRead_7919_compile :
    Func.compile vaultTable 7919 (mintRead) = some (prorataWethVaultCodeChunk30.drop 239 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 214) := by
  rw [mintRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk30.drop 239 ++ prorataWethVaultCodeChunk31.take 7 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk31.drop 11 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 210) : Bytes).length = 1223 := by decide +kernel
  have hbranch := compile_branch vaultTable 7943 9170 _ _
    (prorataWethVaultCodeChunk31.drop 11 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 210) [0x5f, 0x5f, 0xfd]
    mintReturnSize_7947_compile (by rw [hlen]) (by decide) (revert_compile_at 9171)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (9170 >>> 8).toUInt8, Nat.toUInt8 9170, 0x57] : Bytes) = (prorataWethVaultCodeChunk31.drop 7).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk35.drop 210).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk35.drop 211).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk31.take 7) ++ ((prorataWethVaultCodeChunk31.drop 7).take 4) = prorataWethVaultCodeChunk31.take 11 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk31) (i := 7) (j := 4)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk31.take 7), hj0]
  have hj1 : (prorataWethVaultCodeChunk31.take 11) ++ (prorataWethVaultCodeChunk31.drop 11) = prorataWethVaultCodeChunk31 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk31)
  rw [← List.append_assoc (prorataWethVaultCodeChunk31.take 11), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 210) ++ ((prorataWethVaultCodeChunk35.drop 210).take 1) = prorataWethVaultCodeChunk35.take 211 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 210) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 210), hj2]
  have hj3 : (prorataWethVaultCodeChunk35.take 211) ++ ((prorataWethVaultCodeChunk35.drop 211).take 3) = prorataWethVaultCodeChunk35.take 214 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 211) (j := 3)).symm
  rw [hj3]

private theorem mintArgs_7905_compile :
    Func.compile vaultTable 7905 (mintArgs) = some (prorataWethVaultCodeChunk30.drop 225 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 214) := by
  have hb0 : depositArgsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk30.drop 225).take 14 := by
    rfl
  rw [mintArgs]
  rw [compile_prepend, depositArgsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [mintRead_7919_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 225).take 14) ++ (prorataWethVaultCodeChunk30.drop 239) = prorataWethVaultCodeChunk30.drop 225 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 14 (prorataWethVaultCodeChunk30.drop 225)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 225).take 14), hj0]

private theorem mintStatic_7897_compile :
    Func.compile vaultTable 7897 (mintStatic) = some (prorataWethVaultCodeChunk30.drop 217 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) := by
  rw [mintStatic, compile_prepend, depositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : depositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk30.drop 217).take 4 := by
    rfl
  have hlen : ((prorataWethVaultCodeChunk30.drop 225 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 214) : Bytes).length = 1269 := by decide +kernel
  have hbranch := compile_branch vaultTable 7901 9174 _ _
    (prorataWethVaultCodeChunk30.drop 225 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 214) [0x5f, 0x5f, 0xfd]
    mintArgs_7905_compile (by rw [hlen]) (by decide) (revert_compile_at 9175)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (9174 >>> 8).toUInt8, Nat.toUInt8 9174, 0x57] : Bytes) = (prorataWethVaultCodeChunk30.drop 221).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk35.drop 214).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk35.drop 215).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 217).take 4) ++ ((prorataWethVaultCodeChunk30.drop 221).take 4) = (prorataWethVaultCodeChunk30.drop 217).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 217) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 217).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk30.drop 217).take 8) ++ (prorataWethVaultCodeChunk30.drop 225) = prorataWethVaultCodeChunk30.drop 217 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk30.drop 217)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 217).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 214) ++ ((prorataWethVaultCodeChunk35.drop 214).take 1) = prorataWethVaultCodeChunk35.take 215 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 214) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 214), hj2]
  have hj3 : (prorataWethVaultCodeChunk35.take 215) ++ ((prorataWethVaultCodeChunk35.drop 215).take 3) = prorataWethVaultCodeChunk35.take 218 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 215) (j := 3)).symm
  rw [hj3]

private theorem mint_source_cut : ProrataWethVault.routed 2 ProrataWethVault.mint = nonpayable mintStatic := by rfl
private theorem mint_endpoint_compile :
    Func.compile vaultTable 7887 (ProrataWethVault.routed 2 ProrataWethVault.mint) = some (prorataWethVaultCodeChunk30.drop 207 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) := by
  rw [mint_source_cut]
  have hcut : nonpayable mintStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert mintStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 7889 7896 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk30.drop 217 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218)
    (revert_compile_at 7893) (by rfl) (by decide) mintStatic_7897_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (7896 >>> 8).toUInt8, Nat.toUInt8 7896, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk30.drop 207).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (7896 >>> 8).toUInt8, Nat.toUInt8 7896, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 207).take 10) ++ (prorataWethVaultCodeChunk30.drop 217) = prorataWethVaultCodeChunk30.drop 207 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk30.drop 207)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 207).take 10), hj0]

private theorem withdrawWide_source_cut :
    ProrataWethVault.divideWide .up ProrataWethVault.withdrawAfterQuoteSlot =
      wideGuardPrefix +++ Func.branch Func.revert
        (ProrataWethVault.divideWideCore .up ProrataWethVault.withdrawAfterQuoteSlot) := by rfl
private def withdrawNonzero : Func := highZeroPrefix +++ Func.branch
  (ProrataWethVault.divideWide .up ProrataWethVault.withdrawAfterQuoteSlot)
  (ProrataWethVault.divideSimple .up ProrataWethVault.withdrawAfterQuoteSlot)
private theorem withdrawDivide_source_cut :
    ProrataWethVault.divide512 .up ProrataWethVault.withdrawAfterQuoteSlot =
      denominatorZeroPrefix +++ Func.branch withdrawNonzero Func.revert := by rfl

private theorem withdrawFinish_6094_compile :
    Func.compile vaultTable 6094 (ProrataWethVault.finishQuotient .up ProrataWethVault.withdrawAfterQuoteSlot) =
      some ((prorataWethVaultCodeChunk23.drop 206).take 40) := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, isMax, prepend]
  simp only [Func.compile, vault_table_withdrawAfterQuote]
  rfl

private theorem withdrawWideCore_5747_compile :
    Func.compile vaultTable 5747 (ProrataWethVault.divideWideCore .up ProrataWethVault.withdrawAfterQuoteSlot) =
      some (prorataWethVaultCodeChunk22.drop 115 ++ prorataWethVaultCodeChunk23.take 246) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk22.drop 115).take 117 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk22.drop 232 ++ prorataWethVaultCodeChunk23.take 67 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk23.drop 67).take 126 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk23.drop 67).take 63 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk23.drop 130).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : ((prorataWethVaultCodeChunk23.drop 67).take 63) ++ ((prorataWethVaultCodeChunk23.drop 130).take 63) = (prorataWethVaultCodeChunk23.drop 67).take 126 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk23.drop 67) (i := 63) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk23.drop 193).take 13 := by rfl
  have hcomp := divideWideCore_compile_from_finish 5747 .up ProrataWethVault.withdrawAfterQuoteSlot
    ((prorataWethVaultCodeChunk23.drop 206).take 40) withdrawFinish_6094_compile
  rw [hcomp, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk22.drop 115).take 117) ++ (prorataWethVaultCodeChunk22.drop 232) = prorataWethVaultCodeChunk22.drop 115 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 117 (prorataWethVaultCodeChunk22.drop 115)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 115).take 117), hj0]
  have hj1 : (prorataWethVaultCodeChunk23.take 67) ++ ((prorataWethVaultCodeChunk23.drop 67).take 126) = prorataWethVaultCodeChunk23.take 193 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk23) (i := 67) (j := 126)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk23.take 67), hj1]
  have hj2 : (prorataWethVaultCodeChunk23.take 193) ++ ((prorataWethVaultCodeChunk23.drop 193).take 13) = prorataWethVaultCodeChunk23.take 206 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk23) (i := 193) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk23.take 193), hj2]
  have hj3 : (prorataWethVaultCodeChunk23.take 206) ++ ((prorataWethVaultCodeChunk23.drop 206).take 40) = prorataWethVaultCodeChunk23.take 246 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk23) (i := 206) (j := 40)).symm
  rw [hj3]

private theorem withdrawSimple_6135_compile :
    Func.compile vaultTable 6135 (ProrataWethVault.divideSimple .up ProrataWethVault.withdrawAfterQuoteSlot) =
      some (prorataWethVaultCodeChunk23.drop 247 ++ prorataWethVaultCodeChunk24.take 57) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, isMax, prepend]
  simp only [Func.compile, vault_table_withdrawAfterQuote]
  rfl

private theorem withdrawWide_5730_compile :
    Func.compile vaultTable 5730 (ProrataWethVault.divideWide .up ProrataWethVault.withdrawAfterQuoteSlot) = some (prorataWethVaultCodeChunk22.drop 98 ++ prorataWethVaultCodeChunk23.take 246) := by
  rw [withdrawWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk22.drop 98).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ([0x5f, 0x5f, 0xfd] : Bytes).length = 3 := by rfl
  have hbranch := compile_branch vaultTable 5739 5746 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk22.drop 115 ++ prorataWethVaultCodeChunk23.take 246)
    (revert_compile_at 5743) (by rw [hlen]) (by decide) withdrawWideCore_5747_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (5746 >>> 8).toUInt8, Nat.toUInt8 5746, 0x57] : Bytes) = (prorataWethVaultCodeChunk22.drop 107).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk22.drop 114).take 1 := by rfl
  rw [hheader, hjump]
  have hpbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk22.drop 111).take 3 := by rfl
  rw [hpbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk22.drop 98).take 9) ++ ((prorataWethVaultCodeChunk22.drop 107).take 4) = (prorataWethVaultCodeChunk22.drop 98).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk22.drop 98) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 98).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk22.drop 98).take 13) ++ ((prorataWethVaultCodeChunk22.drop 111).take 3) = (prorataWethVaultCodeChunk22.drop 98).take 16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk22.drop 98) (i := 13) (j := 3)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 98).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk22.drop 98).take 16) ++ ((prorataWethVaultCodeChunk22.drop 114).take 1) = (prorataWethVaultCodeChunk22.drop 98).take 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk22.drop 98) (i := 16) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 98).take 16), hj2]
  have hj3 : ((prorataWethVaultCodeChunk22.drop 98).take 17) ++ (prorataWethVaultCodeChunk22.drop 115) = prorataWethVaultCodeChunk22.drop 98 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 17 (prorataWethVaultCodeChunk22.drop 98)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 98).take 17), hj3]

private theorem withdrawNonzero_5721_compile :
    Func.compile vaultTable 5721 (withdrawNonzero) = some (prorataWethVaultCodeChunk22.drop 89 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 57) := by
  rw [withdrawNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk22.drop 89).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk22.drop 98 ++ prorataWethVaultCodeChunk23.take 246) : Bytes).length = 404 := by decide +kernel
  have hbranch := compile_branch vaultTable 5726 6134 _ _
    (prorataWethVaultCodeChunk22.drop 98 ++ prorataWethVaultCodeChunk23.take 246) (prorataWethVaultCodeChunk23.drop 247 ++ prorataWethVaultCodeChunk24.take 57)
    withdrawWide_5730_compile (by rw [hlen]) (by decide) withdrawSimple_6135_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (6134 >>> 8).toUInt8, Nat.toUInt8 6134, 0x57] : Bytes) = (prorataWethVaultCodeChunk22.drop 94).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk23.drop 246).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk22.drop 89).take 5) ++ ((prorataWethVaultCodeChunk22.drop 94).take 4) = (prorataWethVaultCodeChunk22.drop 89).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk22.drop 89) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 89).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk22.drop 89).take 9) ++ (prorataWethVaultCodeChunk22.drop 98) = prorataWethVaultCodeChunk22.drop 89 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk22.drop 89)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 89).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk23.take 246) ++ ((prorataWethVaultCodeChunk23.drop 246).take 1) = prorataWethVaultCodeChunk23.take 247 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk23) (i := 246) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk23.take 246), hj2]
  have hj3 : (prorataWethVaultCodeChunk23.take 247) ++ (prorataWethVaultCodeChunk23.drop 247) = prorataWethVaultCodeChunk23 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 247 (prorataWethVaultCodeChunk23)
  rw [← List.append_assoc (prorataWethVaultCodeChunk23.take 247), hj3]

private theorem withdrawDivide_5712_compile :
    Func.compile vaultTable 5712 (ProrataWethVault.divide512 .up ProrataWethVault.withdrawAfterQuoteSlot) = some (prorataWethVaultCodeChunk22.drop 80 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 61) := by
  rw [withdrawDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk22.drop 80).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk22.drop 89 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 57) : Bytes).length = 480 := by decide +kernel
  have hbranch := compile_branch vaultTable 5717 6201 _ _
    (prorataWethVaultCodeChunk22.drop 89 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 57) [0x5f, 0x5f, 0xfd]
    withdrawNonzero_5721_compile (by rw [hlen]) (by decide) (revert_compile_at 6202)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (6201 >>> 8).toUInt8, Nat.toUInt8 6201, 0x57] : Bytes) = (prorataWethVaultCodeChunk22.drop 85).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk24.drop 57).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk24.drop 58).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk22.drop 80).take 5) ++ ((prorataWethVaultCodeChunk22.drop 85).take 4) = (prorataWethVaultCodeChunk22.drop 80).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk22.drop 80) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 80).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk22.drop 80).take 9) ++ (prorataWethVaultCodeChunk22.drop 89) = prorataWethVaultCodeChunk22.drop 80 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk22.drop 80)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk22.drop 80).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk24.take 57) ++ ((prorataWethVaultCodeChunk24.drop 57).take 1) = prorataWethVaultCodeChunk24.take 58 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 57) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 57), hj2]
  have hj3 : (prorataWethVaultCodeChunk24.take 58) ++ ((prorataWethVaultCodeChunk24.drop 58).take 3) = prorataWethVaultCodeChunk24.take 61 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 58) (j := 3)).symm
  rw [hj3]

private theorem withdrawFinish_6340_compile :
    Func.compile vaultTable 6340 (ProrataWethVault.finishQuotient .up ProrataWethVault.withdrawAfterQuoteSlot) =
      some ((prorataWethVaultCodeChunk24.drop 196).take 40) := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, isMax, prepend]
  simp only [Func.compile, vault_table_withdrawAfterQuote]
  rfl

open ProrataWethVault in
private theorem withdrawProduct_source_cut : productOverTwoPow256 (loadWord amountWord) stagedDenominator .up withdrawAfterQuoteSlot =
    depositMultiplyStage +++ maxDepositMulRecover +++ depositProductTail +++ finishQuotient .up withdrawAfterQuoteSlot := by rfl

open ProrataWethVault in
private theorem withdrawMul_source_cut : mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor .up withdrawAfterQuoteSlot =
    depositMulStage +++ maxDepositMulRecover +++ divide512 .up withdrawAfterQuoteSlot := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def withdrawArithmetic : Func := Func.branch (mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor .up withdrawAfterQuoteSlot) (productOverTwoPow256 (loadWord amountWord) stagedDenominator .up withdrawAfterQuoteSlot)

open ProrataWethVault Jaune.Ninst Ninst in
private def withdrawAssets : Func := previewRedeemAssetsPrefix +++ withdrawArithmetic

open ProrataWethVault Jaune.Ninst Ninst in
private def withdrawStage : Func := previewRedeemStagePrefix +++ Func.branch withdrawAssets Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def withdrawReturnSize : Func := maxDepositReturnSizePrefix +++ Func.branch withdrawStage Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def withdrawRead : Func := maxDepositReadPrefix +++ Func.branch withdrawReturnSize Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def withdrawArgs : Func := mutationArgs3Prefix +++ withdrawRead

open ProrataWethVault Jaune.Ninst Ninst in
private def withdrawStatic : Func := transferStaticPrefix +++ Func.branch withdrawArgs Func.revert

open ProrataWethVault in
private theorem withdrawMul_5583_compile :
    Func.compile vaultTable 5583 (mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor .up withdrawAfterQuoteSlot) = some (prorataWethVaultCodeChunk21.drop 207 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 61) := by
  have hb0 : depositMulStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk21.drop 207).take 44 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = prorataWethVaultCodeChunk21.drop 251 ++ prorataWethVaultCodeChunk22.take 80 := by
    rfl
  rw [withdrawMul_source_cut]
  rw [compile_prepend, depositMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [withdrawDivide_5712_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 207).take 44) ++ (prorataWethVaultCodeChunk21.drop 251) = prorataWethVaultCodeChunk21.drop 207 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 44 (prorataWethVaultCodeChunk21.drop 207)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 207).take 44), hj0]
  have hj1 : (prorataWethVaultCodeChunk22.take 80) ++ (prorataWethVaultCodeChunk22.drop 80) = prorataWethVaultCodeChunk22 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 80 (prorataWethVaultCodeChunk22)
  rw [← List.append_assoc (prorataWethVaultCodeChunk22.take 80), hj1]

open ProrataWethVault in
private theorem withdrawProduct_6206_compile :
    Func.compile vaultTable 6206 (productOverTwoPow256 (loadWord amountWord) stagedDenominator .up withdrawAfterQuoteSlot) = some ((prorataWethVaultCodeChunk24.drop 62).take 174) := by
  have hb0 : depositMultiplyStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk24.drop 62).take 33 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk24.drop 95).take 85 := by
    rfl
  have hb2 : depositProductTail.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk24.drop 180).take 16 := by
    rfl
  rw [withdrawProduct_source_cut]
  rw [compile_prepend, depositMultiplyStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, depositProductTail_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [withdrawFinish_6340_compile, hb0, hb1, hb2]
  simp only [bind, Option.bind, pure, Pure.pure]
  have hj0 : ((prorataWethVaultCodeChunk24.drop 62).take 33) ++ ((prorataWethVaultCodeChunk24.drop 95).take 85) = (prorataWethVaultCodeChunk24.drop 62).take 118 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24.drop 62) (i := 33) (j := 85)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk24.drop 62).take 33), hj0]
  have hj1 : ((prorataWethVaultCodeChunk24.drop 62).take 118) ++ ((prorataWethVaultCodeChunk24.drop 180).take 16) = (prorataWethVaultCodeChunk24.drop 62).take 134 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24.drop 62) (i := 118) (j := 16)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk24.drop 62).take 118), hj1]
  have hj2 : ((prorataWethVaultCodeChunk24.drop 62).take 134) ++ ((prorataWethVaultCodeChunk24.drop 196).take 40) = (prorataWethVaultCodeChunk24.drop 62).take 174 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24.drop 62) (i := 134) (j := 40)).symm
  rw [hj2]

private theorem withdrawArithmetic_5579_compile :
    Func.compile vaultTable 5579 (withdrawArithmetic) = some (prorataWethVaultCodeChunk21.drop 203 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 236) := by
  rw [withdrawArithmetic]
  have hlen : ((prorataWethVaultCodeChunk21.drop 207 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 61) : Bytes).length = 622 := by decide +kernel
  have hbranch := compile_branch vaultTable 5579 6205 _ _
    (prorataWethVaultCodeChunk21.drop 207 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 61) ((prorataWethVaultCodeChunk24.drop 62).take 174)
    withdrawMul_5583_compile (by rw [hlen]) (by decide) withdrawProduct_6206_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (6205 >>> 8).toUInt8, Nat.toUInt8 6205, 0x57] : Bytes) = (prorataWethVaultCodeChunk21.drop 203).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk24.drop 61).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 203).take 4) ++ (prorataWethVaultCodeChunk21.drop 207) = prorataWethVaultCodeChunk21.drop 203 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk21.drop 203)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 203).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk24.take 61) ++ ((prorataWethVaultCodeChunk24.drop 61).take 1) = prorataWethVaultCodeChunk24.take 62 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 61) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 61), hj1]
  have hj2 : (prorataWethVaultCodeChunk24.take 62) ++ ((prorataWethVaultCodeChunk24.drop 62).take 174) = prorataWethVaultCodeChunk24.take 236 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 62) (j := 174)).symm
  rw [hj2]

private theorem withdrawAssets_5573_compile :
    Func.compile vaultTable 5573 (withdrawAssets) = some (prorataWethVaultCodeChunk21.drop 197 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 236) := by
  have hb0 : previewRedeemAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk21.drop 197).take 6 := by
    rw [previewRedeemAssetsPrefix_bytes]
    rfl
  rw [withdrawAssets]
  rw [compile_prepend, previewRedeemAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [withdrawArithmetic_5579_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 197).take 6) ++ (prorataWethVaultCodeChunk21.drop 203) = prorataWethVaultCodeChunk21.drop 197 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 6 (prorataWethVaultCodeChunk21.drop 197)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 197).take 6), hj0]

private theorem withdrawStage_5518_compile :
    Func.compile vaultTable 5518 (withdrawStage) = some (prorataWethVaultCodeChunk21.drop 142 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 240) := by
  rw [withdrawStage, compile_prepend, previewRedeemStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : previewRedeemStagePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk21.drop 142).take 51 := by
    rw [previewRedeemStagePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk21.drop 197 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 236) : Bytes).length = 807 := by decide +kernel
  have hbranch := compile_branch vaultTable 5569 6380 _ _
    (prorataWethVaultCodeChunk21.drop 197 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 236) [0x5f, 0x5f, 0xfd]
    withdrawAssets_5573_compile (by rw [hlen]) (by decide) (revert_compile_at 6381)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (6380 >>> 8).toUInt8, Nat.toUInt8 6380, 0x57] : Bytes) = (prorataWethVaultCodeChunk21.drop 193).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk24.drop 236).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk24.drop 237).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 142).take 51) ++ ((prorataWethVaultCodeChunk21.drop 193).take 4) = (prorataWethVaultCodeChunk21.drop 142).take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21.drop 142) (i := 51) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 142).take 51), hj0]
  have hj1 : ((prorataWethVaultCodeChunk21.drop 142).take 55) ++ (prorataWethVaultCodeChunk21.drop 197) = prorataWethVaultCodeChunk21.drop 142 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 55 (prorataWethVaultCodeChunk21.drop 142)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 142).take 55), hj1]
  have hj2 : (prorataWethVaultCodeChunk24.take 236) ++ ((prorataWethVaultCodeChunk24.drop 236).take 1) = prorataWethVaultCodeChunk24.take 237 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 236) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 236), hj2]
  have hj3 : (prorataWethVaultCodeChunk24.take 237) ++ ((prorataWethVaultCodeChunk24.drop 237).take 3) = prorataWethVaultCodeChunk24.take 240 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 237) (j := 3)).symm
  rw [hj3]

private theorem withdrawReturnSize_5509_compile :
    Func.compile vaultTable 5509 (withdrawReturnSize) = some (prorataWethVaultCodeChunk21.drop 133 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 244) := by
  rw [withdrawReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk21.drop 133).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk21.drop 142 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 240) : Bytes).length = 866 := by decide +kernel
  have hbranch := compile_branch vaultTable 5514 6384 _ _
    (prorataWethVaultCodeChunk21.drop 142 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 240) [0x5f, 0x5f, 0xfd]
    withdrawStage_5518_compile (by rw [hlen]) (by decide) (revert_compile_at 6385)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (6384 >>> 8).toUInt8, Nat.toUInt8 6384, 0x57] : Bytes) = (prorataWethVaultCodeChunk21.drop 138).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk24.drop 240).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk24.drop 241).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 133).take 5) ++ ((prorataWethVaultCodeChunk21.drop 138).take 4) = (prorataWethVaultCodeChunk21.drop 133).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21.drop 133) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 133).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk21.drop 133).take 9) ++ (prorataWethVaultCodeChunk21.drop 142) = prorataWethVaultCodeChunk21.drop 133 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk21.drop 133)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 133).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk24.take 240) ++ ((prorataWethVaultCodeChunk24.drop 240).take 1) = prorataWethVaultCodeChunk24.take 241 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 240) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 240), hj2]
  have hj3 : (prorataWethVaultCodeChunk24.take 241) ++ ((prorataWethVaultCodeChunk24.drop 241).take 3) = prorataWethVaultCodeChunk24.take 244 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 241) (j := 3)).symm
  rw [hj3]

private theorem withdrawRead_5481_compile :
    Func.compile vaultTable 5481 (withdrawRead) = some (prorataWethVaultCodeChunk21.drop 105 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 248) := by
  rw [withdrawRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk21.drop 105).take 24 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk21.drop 133 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 244) : Bytes).length = 879 := by decide +kernel
  have hbranch := compile_branch vaultTable 5505 6388 _ _
    (prorataWethVaultCodeChunk21.drop 133 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 244) [0x5f, 0x5f, 0xfd]
    withdrawReturnSize_5509_compile (by rw [hlen]) (by decide) (revert_compile_at 6389)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (6388 >>> 8).toUInt8, Nat.toUInt8 6388, 0x57] : Bytes) = (prorataWethVaultCodeChunk21.drop 129).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk24.drop 244).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk24.drop 245).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 105).take 24) ++ ((prorataWethVaultCodeChunk21.drop 129).take 4) = (prorataWethVaultCodeChunk21.drop 105).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21.drop 105) (i := 24) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 105).take 24), hj0]
  have hj1 : ((prorataWethVaultCodeChunk21.drop 105).take 28) ++ (prorataWethVaultCodeChunk21.drop 133) = prorataWethVaultCodeChunk21.drop 105 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 28 (prorataWethVaultCodeChunk21.drop 105)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 105).take 28), hj1]
  have hj2 : (prorataWethVaultCodeChunk24.take 244) ++ ((prorataWethVaultCodeChunk24.drop 244).take 1) = prorataWethVaultCodeChunk24.take 245 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 244) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 244), hj2]
  have hj3 : (prorataWethVaultCodeChunk24.take 245) ++ ((prorataWethVaultCodeChunk24.drop 245).take 3) = prorataWethVaultCodeChunk24.take 248 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 245) (j := 3)).symm
  rw [hj3]

private theorem withdrawArgs_5460_compile :
    Func.compile vaultTable 5460 (withdrawArgs) = some (prorataWethVaultCodeChunk21.drop 84 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 248) := by
  have hb0 : mutationArgs3Prefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk21.drop 84).take 21 := by
    rfl
  rw [withdrawArgs]
  rw [compile_prepend, mutationArgs3Prefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [withdrawRead_5481_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 84).take 21) ++ (prorataWethVaultCodeChunk21.drop 105) = prorataWethVaultCodeChunk21.drop 84 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 21 (prorataWethVaultCodeChunk21.drop 84)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 84).take 21), hj0]

private theorem withdrawStatic_5452_compile :
    Func.compile vaultTable 5452 (withdrawStatic) = some (prorataWethVaultCodeChunk21.drop 76 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 252) := by
  rw [withdrawStatic, compile_prepend, transferStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : transferStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk21.drop 76).take 4 := by
    rfl
  have hlen : ((prorataWethVaultCodeChunk21.drop 84 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 248) : Bytes).length = 932 := by decide +kernel
  have hbranch := compile_branch vaultTable 5456 6392 _ _
    (prorataWethVaultCodeChunk21.drop 84 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 248) [0x5f, 0x5f, 0xfd]
    withdrawArgs_5460_compile (by rw [hlen]) (by decide) (revert_compile_at 6393)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (6392 >>> 8).toUInt8, Nat.toUInt8 6392, 0x57] : Bytes) = (prorataWethVaultCodeChunk21.drop 80).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk24.drop 248).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk24.drop 249).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 76).take 4) ++ ((prorataWethVaultCodeChunk21.drop 80).take 4) = (prorataWethVaultCodeChunk21.drop 76).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21.drop 76) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 76).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk21.drop 76).take 8) ++ (prorataWethVaultCodeChunk21.drop 84) = prorataWethVaultCodeChunk21.drop 76 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk21.drop 76)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 76).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk24.take 248) ++ ((prorataWethVaultCodeChunk24.drop 248).take 1) = prorataWethVaultCodeChunk24.take 249 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 248) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 248), hj2]
  have hj3 : (prorataWethVaultCodeChunk24.take 249) ++ ((prorataWethVaultCodeChunk24.drop 249).take 3) = prorataWethVaultCodeChunk24.take 252 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 249) (j := 3)).symm
  rw [hj3]

private theorem withdraw_source_cut : ProrataWethVault.routed 3 ProrataWethVault.withdraw = nonpayable withdrawStatic := by rfl
private theorem withdraw_endpoint_compile :
    Func.compile vaultTable 5442 (ProrataWethVault.routed 3 ProrataWethVault.withdraw) = some (prorataWethVaultCodeChunk21.drop 66 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 252) := by
  rw [withdraw_source_cut]
  have hcut : nonpayable withdrawStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert withdrawStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 5444 5451 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk21.drop 76 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 252)
    (revert_compile_at 5448) (by rfl) (by decide) withdrawStatic_5452_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (5451 >>> 8).toUInt8, Nat.toUInt8 5451, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk21.drop 66).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (5451 >>> 8).toUInt8, Nat.toUInt8 5451, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 66).take 10) ++ (prorataWethVaultCodeChunk21.drop 76) = prorataWethVaultCodeChunk21.drop 66 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk21.drop 66)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 66).take 10), hj0]

private theorem maxWithdrawFinish_compile_at (n : Nat) :
    Func.compile vaultTable n (ProrataWethVault.finishQuotient .capDown ProrataWethVault.returnWordSlot) =
      some [0x61, 0x03, 0x00, 0x51, 0x61, 0x3d, 0x33, 0x56] := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl
private theorem maxWithdrawCore_compile_at (n : Nat) :
    Func.compile vaultTable n (ProrataWethVault.divideWideCore .capDown ProrataWethVault.returnWordSlot) =
      some (wideCorePrefix.flatMap Ninst.toBytes ++ ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes ++
        wideCoreSuffix.flatMap Ninst.toBytes ++ [0x61, 0x03, 0x00, 0x51, 0x61, 0x3d, 0x33, 0x56]) := by
  exact divideWideCore_compile_from_finish n .capDown ProrataWethVault.returnWordSlot _
    (maxWithdrawFinish_compile_at (n + 347))
private theorem maxWithdrawWide_source_cut :
    ProrataWethVault.divideWide .capDown ProrataWethVault.returnWordSlot =
      wideGuardPrefix +++ Func.branch
        (ProrataWethVault.divisionOverflow .capDown ProrataWethVault.returnWordSlot)
        (ProrataWethVault.divideWideCore .capDown ProrataWethVault.returnWordSlot) := by rfl
private def maxWithdrawNonzero : Func := highZeroPrefix +++ Func.branch
  (ProrataWethVault.divideWide .capDown ProrataWethVault.returnWordSlot)
  (ProrataWethVault.divideSimple .capDown ProrataWethVault.returnWordSlot)
private theorem maxWithdrawDivide_source_cut :
    ProrataWethVault.divide512 .capDown ProrataWethVault.returnWordSlot =
      denominatorZeroPrefix +++ Func.branch maxWithdrawNonzero Func.revert := by rfl

private theorem maxWithdrawCore_1456_compile :
    Func.compile vaultTable 1456
      (ProrataWethVault.divideWideCore .capDown ProrataWethVault.returnWordSlot) =
      some (prorataWethVaultCodeChunk5.drop 176 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 19) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk5.drop 176 ++ prorataWethVaultCodeChunk6.take 37 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk6.drop 37).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk6.drop 128).take 126 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk6.drop 128).take 63 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk6.drop 191).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : ((prorataWethVaultCodeChunk6.drop 128).take 63) ++ ((prorataWethVaultCodeChunk6.drop 191).take 63) = (prorataWethVaultCodeChunk6.drop 128).take 126 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk6.drop 128) (i := 63) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk6.drop 254 ++ prorataWethVaultCodeChunk7.take 11 := by rfl
  have hfinish : ([0x61, 0x03, 0x00, 0x51, 0x61, 0x3d, 0x33, 0x56] : Bytes) = (prorataWethVaultCodeChunk7.drop 11).take 8 := by rfl
  rw [maxWithdrawCore_compile_at, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs, hfinish]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk6.take 37) ++ ((prorataWethVaultCodeChunk6.drop 37).take 91) = prorataWethVaultCodeChunk6.take 128 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk6) (i := 37) (j := 91)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk6.take 37), hj0]
  have hj1 : (prorataWethVaultCodeChunk6.take 128) ++ ((prorataWethVaultCodeChunk6.drop 128).take 126) = prorataWethVaultCodeChunk6.take 254 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk6) (i := 128) (j := 126)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk6.take 128), hj1]
  have hj2 : (prorataWethVaultCodeChunk6.take 254) ++ (prorataWethVaultCodeChunk6.drop 254) = prorataWethVaultCodeChunk6 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 254 (prorataWethVaultCodeChunk6)
  rw [← List.append_assoc (prorataWethVaultCodeChunk6.take 254), hj2]
  have hj3 : (prorataWethVaultCodeChunk7.take 11) ++ ((prorataWethVaultCodeChunk7.drop 11).take 8) = prorataWethVaultCodeChunk7.take 19 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7) (i := 11) (j := 8)).symm
  rw [hj3]

private theorem maxWithdrawOverflow_1418_compile :
    Func.compile vaultTable 1418 (ProrataWethVault.divisionOverflow .capDown ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk5.drop 138).take 37) := by
  simp only [ProrataWethVault.divisionOverflow, Func.compile, vault_table_returnWord]
  rfl
private theorem maxWithdrawSimple_1812_compile :
    Func.compile vaultTable 1812 (ProrataWethVault.divideSimple .capDown ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk7.drop 20).take 34) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem maxWithdrawWide_1405_compile :
    Func.compile vaultTable 1405 (ProrataWethVault.divideWide .capDown ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk5.drop 125 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 19) := by
  rw [maxWithdrawWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk5.drop 125).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : (((prorataWethVaultCodeChunk5.drop 138).take 37) : Bytes).length = 37 := by decide +kernel
  have hbranch := compile_branch vaultTable 1414 1455 _ _
    ((prorataWethVaultCodeChunk5.drop 138).take 37) (prorataWethVaultCodeChunk5.drop 176 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 19)
    maxWithdrawOverflow_1418_compile (by rw [hlen]) (by decide) maxWithdrawCore_1456_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1455 >>> 8).toUInt8, Nat.toUInt8 1455, 0x57] : Bytes) = (prorataWethVaultCodeChunk5.drop 134).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk5.drop 175).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk5.drop 125).take 9) ++ ((prorataWethVaultCodeChunk5.drop 134).take 4) = (prorataWethVaultCodeChunk5.drop 125).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk5.drop 125) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 125).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk5.drop 125).take 13) ++ ((prorataWethVaultCodeChunk5.drop 138).take 37) = (prorataWethVaultCodeChunk5.drop 125).take 50 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk5.drop 125) (i := 13) (j := 37)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 125).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk5.drop 125).take 50) ++ ((prorataWethVaultCodeChunk5.drop 175).take 1) = (prorataWethVaultCodeChunk5.drop 125).take 51 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk5.drop 125) (i := 50) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 125).take 50), hj2]
  have hj3 : ((prorataWethVaultCodeChunk5.drop 125).take 51) ++ (prorataWethVaultCodeChunk5.drop 176) = prorataWethVaultCodeChunk5.drop 125 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 51 (prorataWethVaultCodeChunk5.drop 125)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 125).take 51), hj3]

private theorem maxWithdrawNonzero_1396_compile :
    Func.compile vaultTable 1396 (maxWithdrawNonzero) = some (prorataWethVaultCodeChunk5.drop 116 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 54) := by
  rw [maxWithdrawNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk5.drop 116).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk5.drop 125 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 19) : Bytes).length = 406 := by decide +kernel
  have hbranch := compile_branch vaultTable 1401 1811 _ _
    (prorataWethVaultCodeChunk5.drop 125 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 19) ((prorataWethVaultCodeChunk7.drop 20).take 34)
    maxWithdrawWide_1405_compile (by rw [hlen]) (by decide) maxWithdrawSimple_1812_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1811 >>> 8).toUInt8, Nat.toUInt8 1811, 0x57] : Bytes) = (prorataWethVaultCodeChunk5.drop 121).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk7.drop 19).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk5.drop 116).take 5) ++ ((prorataWethVaultCodeChunk5.drop 121).take 4) = (prorataWethVaultCodeChunk5.drop 116).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk5.drop 116) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 116).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk5.drop 116).take 9) ++ (prorataWethVaultCodeChunk5.drop 125) = prorataWethVaultCodeChunk5.drop 116 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk5.drop 116)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 116).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk7.take 19) ++ ((prorataWethVaultCodeChunk7.drop 19).take 1) = prorataWethVaultCodeChunk7.take 20 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7) (i := 19) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk7.take 19), hj2]
  have hj3 : (prorataWethVaultCodeChunk7.take 20) ++ ((prorataWethVaultCodeChunk7.drop 20).take 34) = prorataWethVaultCodeChunk7.take 54 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7) (i := 20) (j := 34)).symm
  rw [hj3]

private theorem maxWithdrawDivide_1387_compile :
    Func.compile vaultTable 1387 (ProrataWethVault.divide512 .capDown ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk5.drop 107 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 58) := by
  rw [maxWithdrawDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk5.drop 107).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk5.drop 116 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 54) : Bytes).length = 450 := by decide +kernel
  have hbranch := compile_branch vaultTable 1392 1846 _ _
    (prorataWethVaultCodeChunk5.drop 116 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 54) [0x5f, 0x5f, 0xfd]
    maxWithdrawNonzero_1396_compile (by rw [hlen]) (by decide) (revert_compile_at 1847)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1846 >>> 8).toUInt8, Nat.toUInt8 1846, 0x57] : Bytes) = (prorataWethVaultCodeChunk5.drop 112).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk7.drop 54).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk7.drop 55).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk5.drop 107).take 5) ++ ((prorataWethVaultCodeChunk5.drop 112).take 4) = (prorataWethVaultCodeChunk5.drop 107).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk5.drop 107) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 107).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk5.drop 107).take 9) ++ (prorataWethVaultCodeChunk5.drop 116) = prorataWethVaultCodeChunk5.drop 107 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk5.drop 107)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk5.drop 107).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk7.take 54) ++ ((prorataWethVaultCodeChunk7.drop 54).take 1) = prorataWethVaultCodeChunk7.take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7) (i := 54) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk7.take 54), hj2]
  have hj3 : (prorataWethVaultCodeChunk7.take 55) ++ ((prorataWethVaultCodeChunk7.drop 55).take 3) = prorataWethVaultCodeChunk7.take 58 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7) (i := 55) (j := 3)).symm
  rw [hj3]

private theorem maxWithdrawCore_1945_compile :
    Func.compile vaultTable 1945
      (ProrataWethVault.divideWideCore .capDown ProrataWethVault.returnWordSlot) =
      some (prorataWethVaultCodeChunk7.drop 153 ++ prorataWethVaultCodeChunk8.take 252) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = prorataWethVaultCodeChunk7.drop 153 ++ prorataWethVaultCodeChunk8.take 14 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk8.drop 14).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk8.drop 105).take 126 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk8.drop 105).take 63 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk8.drop 168).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : ((prorataWethVaultCodeChunk8.drop 105).take 63) ++ ((prorataWethVaultCodeChunk8.drop 168).take 63) = (prorataWethVaultCodeChunk8.drop 105).take 126 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk8.drop 105) (i := 63) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk8.drop 231).take 13 := by rfl
  have hfinish : ([0x61, 0x03, 0x00, 0x51, 0x61, 0x3d, 0x33, 0x56] : Bytes) = (prorataWethVaultCodeChunk8.drop 244).take 8 := by rfl
  rw [maxWithdrawCore_compile_at, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs, hfinish]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk8.take 14) ++ ((prorataWethVaultCodeChunk8.drop 14).take 91) = prorataWethVaultCodeChunk8.take 105 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk8) (i := 14) (j := 91)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk8.take 14), hj0]
  have hj1 : (prorataWethVaultCodeChunk8.take 105) ++ ((prorataWethVaultCodeChunk8.drop 105).take 126) = prorataWethVaultCodeChunk8.take 231 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk8) (i := 105) (j := 126)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk8.take 105), hj1]
  have hj2 : (prorataWethVaultCodeChunk8.take 231) ++ ((prorataWethVaultCodeChunk8.drop 231).take 13) = prorataWethVaultCodeChunk8.take 244 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk8) (i := 231) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk8.take 231), hj2]
  have hj3 : (prorataWethVaultCodeChunk8.take 244) ++ ((prorataWethVaultCodeChunk8.drop 244).take 8) = prorataWethVaultCodeChunk8.take 252 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk8) (i := 244) (j := 8)).symm
  rw [hj3]

private theorem maxWithdrawOverflow_1907_compile :
    Func.compile vaultTable 1907 (ProrataWethVault.divisionOverflow .capDown ProrataWethVault.returnWordSlot) =
      some ((prorataWethVaultCodeChunk7.drop 115).take 37) := by
  simp only [ProrataWethVault.divisionOverflow, Func.compile, vault_table_returnWord]
  rfl
private theorem maxWithdrawSimple_2301_compile :
    Func.compile vaultTable 2301 (ProrataWethVault.divideSimple .capDown ProrataWethVault.returnWordSlot) =
      some (prorataWethVaultCodeChunk8.drop 253 ++ prorataWethVaultCodeChunk9.take 31) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, prepend]
  simp only [Func.compile, vault_table_returnWord]
  rfl

private theorem maxWithdrawWide_1894_compile :
    Func.compile vaultTable 1894 (ProrataWethVault.divideWide .capDown ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk7.drop 102 ++ prorataWethVaultCodeChunk8.take 252) := by
  rw [maxWithdrawWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk7.drop 102).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : (((prorataWethVaultCodeChunk7.drop 115).take 37) : Bytes).length = 37 := by decide +kernel
  have hbranch := compile_branch vaultTable 1903 1944 _ _
    ((prorataWethVaultCodeChunk7.drop 115).take 37) (prorataWethVaultCodeChunk7.drop 153 ++ prorataWethVaultCodeChunk8.take 252)
    maxWithdrawOverflow_1907_compile (by rw [hlen]) (by decide) maxWithdrawCore_1945_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (1944 >>> 8).toUInt8, Nat.toUInt8 1944, 0x57] : Bytes) = (prorataWethVaultCodeChunk7.drop 111).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk7.drop 152).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk7.drop 102).take 9) ++ ((prorataWethVaultCodeChunk7.drop 111).take 4) = (prorataWethVaultCodeChunk7.drop 102).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7.drop 102) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 102).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk7.drop 102).take 13) ++ ((prorataWethVaultCodeChunk7.drop 115).take 37) = (prorataWethVaultCodeChunk7.drop 102).take 50 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7.drop 102) (i := 13) (j := 37)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 102).take 13), hj1]
  have hj2 : ((prorataWethVaultCodeChunk7.drop 102).take 50) ++ ((prorataWethVaultCodeChunk7.drop 152).take 1) = (prorataWethVaultCodeChunk7.drop 102).take 51 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7.drop 102) (i := 50) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 102).take 50), hj2]
  have hj3 : ((prorataWethVaultCodeChunk7.drop 102).take 51) ++ (prorataWethVaultCodeChunk7.drop 153) = prorataWethVaultCodeChunk7.drop 102 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 51 (prorataWethVaultCodeChunk7.drop 102)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 102).take 51), hj3]

private theorem maxWithdrawNonzero_1885_compile :
    Func.compile vaultTable 1885 (maxWithdrawNonzero) = some (prorataWethVaultCodeChunk7.drop 93 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 31) := by
  rw [maxWithdrawNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk7.drop 93).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk7.drop 102 ++ prorataWethVaultCodeChunk8.take 252) : Bytes).length = 406 := by decide +kernel
  have hbranch := compile_branch vaultTable 1890 2300 _ _
    (prorataWethVaultCodeChunk7.drop 102 ++ prorataWethVaultCodeChunk8.take 252) (prorataWethVaultCodeChunk8.drop 253 ++ prorataWethVaultCodeChunk9.take 31)
    maxWithdrawWide_1894_compile (by rw [hlen]) (by decide) maxWithdrawSimple_2301_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2300 >>> 8).toUInt8, Nat.toUInt8 2300, 0x57] : Bytes) = (prorataWethVaultCodeChunk7.drop 98).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk8.drop 252).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk7.drop 93).take 5) ++ ((prorataWethVaultCodeChunk7.drop 98).take 4) = (prorataWethVaultCodeChunk7.drop 93).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7.drop 93) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 93).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk7.drop 93).take 9) ++ (prorataWethVaultCodeChunk7.drop 102) = prorataWethVaultCodeChunk7.drop 93 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk7.drop 93)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 93).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk8.take 252) ++ ((prorataWethVaultCodeChunk8.drop 252).take 1) = prorataWethVaultCodeChunk8.take 253 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk8) (i := 252) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk8.take 252), hj2]
  have hj3 : (prorataWethVaultCodeChunk8.take 253) ++ (prorataWethVaultCodeChunk8.drop 253) = prorataWethVaultCodeChunk8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 253 (prorataWethVaultCodeChunk8)
  rw [← List.append_assoc (prorataWethVaultCodeChunk8.take 253), hj3]

private theorem maxWithdrawDivide_1876_compile :
    Func.compile vaultTable 1876 (ProrataWethVault.divide512 .capDown ProrataWethVault.returnWordSlot) = some (prorataWethVaultCodeChunk7.drop 84 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 35) := by
  rw [maxWithdrawDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk7.drop 84).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk7.drop 93 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 31) : Bytes).length = 450 := by decide +kernel
  have hbranch := compile_branch vaultTable 1881 2335 _ _
    (prorataWethVaultCodeChunk7.drop 93 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 31) [0x5f, 0x5f, 0xfd]
    maxWithdrawNonzero_1885_compile (by rw [hlen]) (by decide) (revert_compile_at 2336)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2335 >>> 8).toUInt8, Nat.toUInt8 2335, 0x57] : Bytes) = (prorataWethVaultCodeChunk7.drop 89).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk9.drop 31).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk9.drop 32).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk7.drop 84).take 5) ++ ((prorataWethVaultCodeChunk7.drop 89).take 4) = (prorataWethVaultCodeChunk7.drop 84).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7.drop 84) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 84).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk7.drop 84).take 9) ++ (prorataWethVaultCodeChunk7.drop 93) = prorataWethVaultCodeChunk7.drop 84 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk7.drop 84)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 84).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk9.take 31) ++ ((prorataWethVaultCodeChunk9.drop 31).take 1) = prorataWethVaultCodeChunk9.take 32 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 31) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 31), hj2]
  have hj3 : (prorataWethVaultCodeChunk9.take 32) ++ ((prorataWethVaultCodeChunk9.drop 32).take 3) = prorataWethVaultCodeChunk9.take 35 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 32) (j := 3)).symm
  rw [hj3]

open ProrataWethVault in
private theorem maxWithdrawMul_source_cut : mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .capDown returnWordSlot =
    mutationAssetMulStage +++ maxDepositMulRecover +++ divide512 .capDown returnWordSlot := by rfl
open ProrataWethVault in
private theorem maxWithdrawShift_source_cut : shiftedDiv (loadWord amountWord) stagedDenominator .capDown returnWordSlot =
    mutationShiftStage +++ divide512 .capDown returnWordSlot := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawArithmetic : Func := Func.branch (mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .capDown returnWordSlot) (shiftedDiv (loadWord amountWord) stagedDenominator .capDown returnWordSlot)

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawStagePrefix : Line := arg 0 ++ [sload] ++ mstoreAt amountWord ++ maxDepositSupplyPrefix
private theorem maxWithdrawStagePrefix_size : prefixByteSize maxWithdrawStagePrefix = 53 := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawAssets : Func := maxDepositAssetsPrefix +++ maxWithdrawArithmetic

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawReturnSize : Func := maxDepositReturnSizePrefix +++ Func.branch maxWithdrawAssets Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawRead : Func := maxDepositReadPrefix +++ Func.branch maxWithdrawReturnSize Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawStage : Func := maxWithdrawStagePrefix +++ Func.branch maxWithdrawRead (returnConstant 0)

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawCanonical : Func := maxDepositCanonicalPrefix +++ Func.branch maxWithdrawStage Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def maxWithdrawStatic : Func := maxDepositStaticPrefix +++ Func.branch maxWithdrawCanonical Func.revert

open ProrataWethVault in
private theorem maxWithdrawMul_1258_compile :
    Func.compile vaultTable 1258 (mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator .capDown returnWordSlot) = some (prorataWethVaultCodeChunk4.drop 234 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 58) := by
  have hb0 : mutationAssetMulStage.flatMap Ninst.toBytes = prorataWethVaultCodeChunk4.drop 234 ++ prorataWethVaultCodeChunk5.take 22 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk5.drop 22).take 85 := by
    rfl
  rw [maxWithdrawMul_source_cut]
  rw [compile_prepend, mutationAssetMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [maxWithdrawDivide_1387_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk5.take 22) ++ ((prorataWethVaultCodeChunk5.drop 22).take 85) = prorataWethVaultCodeChunk5.take 107 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk5) (i := 22) (j := 85)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk5.take 22), hj0]
  have hj1 : (prorataWethVaultCodeChunk5.take 107) ++ (prorataWethVaultCodeChunk5.drop 107) = prorataWethVaultCodeChunk5 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 107 (prorataWethVaultCodeChunk5)
  rw [← List.append_assoc (prorataWethVaultCodeChunk5.take 107), hj1]

open ProrataWethVault in
private theorem maxWithdrawShift_1851_compile :
    Func.compile vaultTable 1851 (shiftedDiv (loadWord amountWord) stagedDenominator .capDown returnWordSlot) = some (prorataWethVaultCodeChunk7.drop 59 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 35) := by
  have hb0 : mutationShiftStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk7.drop 59).take 25 := by
    rfl
  rw [maxWithdrawShift_source_cut]
  rw [compile_prepend, mutationShiftStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [maxWithdrawDivide_1876_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk7.drop 59).take 25) ++ (prorataWethVaultCodeChunk7.drop 84) = prorataWethVaultCodeChunk7.drop 59 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 25 (prorataWethVaultCodeChunk7.drop 59)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk7.drop 59).take 25), hj0]

private theorem maxWithdrawArithmetic_1254_compile :
    Func.compile vaultTable 1254 (maxWithdrawArithmetic) = some (prorataWethVaultCodeChunk4.drop 230 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 35) := by
  rw [maxWithdrawArithmetic]
  have hlen : ((prorataWethVaultCodeChunk4.drop 234 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 58) : Bytes).length = 592 := by decide +kernel
  have hbranch := compile_branch vaultTable 1254 1850 _ _
    (prorataWethVaultCodeChunk4.drop 234 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7.take 58) (prorataWethVaultCodeChunk7.drop 59 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 35)
    maxWithdrawMul_1258_compile (by rw [hlen]) (by decide) maxWithdrawShift_1851_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (1850 >>> 8).toUInt8, Nat.toUInt8 1850, 0x57] : Bytes) = (prorataWethVaultCodeChunk4.drop 230).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk7.drop 58).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 230).take 4) ++ (prorataWethVaultCodeChunk4.drop 234) = prorataWethVaultCodeChunk4.drop 230 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk4.drop 230)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 230).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk7.take 58) ++ ((prorataWethVaultCodeChunk7.drop 58).take 1) = prorataWethVaultCodeChunk7.take 59 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk7) (i := 58) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk7.take 58), hj1]
  have hj2 : (prorataWethVaultCodeChunk7.take 59) ++ (prorataWethVaultCodeChunk7.drop 59) = prorataWethVaultCodeChunk7 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 59 (prorataWethVaultCodeChunk7)
  rw [← List.append_assoc (prorataWethVaultCodeChunk7.take 59), hj2]

private theorem maxWithdrawAssets_1242_compile :
    Func.compile vaultTable 1242 (maxWithdrawAssets) = some (prorataWethVaultCodeChunk4.drop 218 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 35) := by
  have hb0 : maxDepositAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk4.drop 218).take 12 := by
    rw [maxDepositAssetsPrefix_bytes]
    rfl
  rw [maxWithdrawAssets]
  rw [compile_prepend, maxDepositAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [maxWithdrawArithmetic_1254_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 218).take 12) ++ (prorataWethVaultCodeChunk4.drop 230) = prorataWethVaultCodeChunk4.drop 218 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 12 (prorataWethVaultCodeChunk4.drop 218)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 218).take 12), hj0]

private theorem maxWithdrawReturnSize_1233_compile :
    Func.compile vaultTable 1233 (maxWithdrawReturnSize) = some (prorataWethVaultCodeChunk4.drop 209 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 39) := by
  rw [maxWithdrawReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk4.drop 209).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk4.drop 218 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 35) : Bytes).length = 1097 := by decide +kernel
  have hbranch := compile_branch vaultTable 1238 2339 _ _
    (prorataWethVaultCodeChunk4.drop 218 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 35) [0x5f, 0x5f, 0xfd]
    maxWithdrawAssets_1242_compile (by rw [hlen]) (by decide) (revert_compile_at 2340)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2339 >>> 8).toUInt8, Nat.toUInt8 2339, 0x57] : Bytes) = (prorataWethVaultCodeChunk4.drop 214).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk9.drop 35).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk9.drop 36).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 209).take 5) ++ ((prorataWethVaultCodeChunk4.drop 214).take 4) = (prorataWethVaultCodeChunk4.drop 209).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4.drop 209) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 209).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk4.drop 209).take 9) ++ (prorataWethVaultCodeChunk4.drop 218) = prorataWethVaultCodeChunk4.drop 209 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk4.drop 209)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 209).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk9.take 35) ++ ((prorataWethVaultCodeChunk9.drop 35).take 1) = prorataWethVaultCodeChunk9.take 36 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 35) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 35), hj2]
  have hj3 : (prorataWethVaultCodeChunk9.take 36) ++ ((prorataWethVaultCodeChunk9.drop 36).take 3) = prorataWethVaultCodeChunk9.take 39 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 36) (j := 3)).symm
  rw [hj3]

private theorem maxWithdrawRead_1205_compile :
    Func.compile vaultTable 1205 (maxWithdrawRead) = some (prorataWethVaultCodeChunk4.drop 181 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 43) := by
  rw [maxWithdrawRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk4.drop 181).take 24 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk4.drop 209 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 39) : Bytes).length = 1110 := by decide +kernel
  have hbranch := compile_branch vaultTable 1229 2343 _ _
    (prorataWethVaultCodeChunk4.drop 209 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 39) [0x5f, 0x5f, 0xfd]
    maxWithdrawReturnSize_1233_compile (by rw [hlen]) (by decide) (revert_compile_at 2344)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2343 >>> 8).toUInt8, Nat.toUInt8 2343, 0x57] : Bytes) = (prorataWethVaultCodeChunk4.drop 205).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk9.drop 39).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk9.drop 40).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 181).take 24) ++ ((prorataWethVaultCodeChunk4.drop 205).take 4) = (prorataWethVaultCodeChunk4.drop 181).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4.drop 181) (i := 24) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 181).take 24), hj0]
  have hj1 : ((prorataWethVaultCodeChunk4.drop 181).take 28) ++ (prorataWethVaultCodeChunk4.drop 209) = prorataWethVaultCodeChunk4.drop 181 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 28 (prorataWethVaultCodeChunk4.drop 181)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 181).take 28), hj1]
  have hj2 : (prorataWethVaultCodeChunk9.take 39) ++ ((prorataWethVaultCodeChunk9.drop 39).take 1) = prorataWethVaultCodeChunk9.take 40 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 39) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 39), hj2]
  have hj3 : (prorataWethVaultCodeChunk9.take 40) ++ ((prorataWethVaultCodeChunk9.drop 40).take 3) = prorataWethVaultCodeChunk9.take 43 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 40) (j := 3)).symm
  rw [hj3]

private theorem maxWithdrawZero_2348_compile :
    Func.compile vaultTable 2348 (ProrataWethVault.returnConstant 0) = some ((prorataWethVaultCodeChunk9.drop 44).take 7) := by
  rw [returnConstant_zero_compile_at]
  rfl

private theorem maxWithdrawStage_1148_compile :
    Func.compile vaultTable 1148 (maxWithdrawStage) = some (prorataWethVaultCodeChunk4.drop 124 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 51) := by
  rw [maxWithdrawStage, compile_prepend, maxWithdrawStagePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxWithdrawStagePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk4.drop 124).take 53 := by
    rfl
  have hlen : ((prorataWethVaultCodeChunk4.drop 181 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 43) : Bytes).length = 1142 := by decide +kernel
  have hbranch := compile_branch vaultTable 1201 2347 _ _
    (prorataWethVaultCodeChunk4.drop 181 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 43) ((prorataWethVaultCodeChunk9.drop 44).take 7)
    maxWithdrawRead_1205_compile (by rw [hlen]) (by decide) maxWithdrawZero_2348_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2347 >>> 8).toUInt8, Nat.toUInt8 2347, 0x57] : Bytes) = (prorataWethVaultCodeChunk4.drop 177).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk9.drop 43).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 124).take 53) ++ ((prorataWethVaultCodeChunk4.drop 177).take 4) = (prorataWethVaultCodeChunk4.drop 124).take 57 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4.drop 124) (i := 53) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 124).take 53), hj0]
  have hj1 : ((prorataWethVaultCodeChunk4.drop 124).take 57) ++ (prorataWethVaultCodeChunk4.drop 181) = prorataWethVaultCodeChunk4.drop 124 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 57 (prorataWethVaultCodeChunk4.drop 124)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 124).take 57), hj1]
  have hj2 : (prorataWethVaultCodeChunk9.take 43) ++ ((prorataWethVaultCodeChunk9.drop 43).take 1) = prorataWethVaultCodeChunk9.take 44 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 43) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 43), hj2]
  have hj3 : (prorataWethVaultCodeChunk9.take 44) ++ ((prorataWethVaultCodeChunk9.drop 44).take 7) = prorataWethVaultCodeChunk9.take 51 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 44) (j := 7)).symm
  rw [hj3]

private theorem maxWithdrawCanonical_1135_compile :
    Func.compile vaultTable 1135 (maxWithdrawCanonical) = some (prorataWethVaultCodeChunk4.drop 111 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 55) := by
  rw [maxWithdrawCanonical, compile_prepend, maxDepositCanonicalPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositCanonicalPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk4.drop 111).take 9 := by
    rw [maxDepositCanonicalPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk4.drop 124 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 51) : Bytes).length = 1207 := by decide +kernel
  have hbranch := compile_branch vaultTable 1144 2355 _ _
    (prorataWethVaultCodeChunk4.drop 124 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 51) [0x5f, 0x5f, 0xfd]
    maxWithdrawStage_1148_compile (by rw [hlen]) (by decide) (revert_compile_at 2356)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2355 >>> 8).toUInt8, Nat.toUInt8 2355, 0x57] : Bytes) = (prorataWethVaultCodeChunk4.drop 120).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk9.drop 51).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk9.drop 52).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 111).take 9) ++ ((prorataWethVaultCodeChunk4.drop 120).take 4) = (prorataWethVaultCodeChunk4.drop 111).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4.drop 111) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 111).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk4.drop 111).take 13) ++ (prorataWethVaultCodeChunk4.drop 124) = prorataWethVaultCodeChunk4.drop 111 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 13 (prorataWethVaultCodeChunk4.drop 111)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 111).take 13), hj1]
  have hj2 : (prorataWethVaultCodeChunk9.take 51) ++ ((prorataWethVaultCodeChunk9.drop 51).take 1) = prorataWethVaultCodeChunk9.take 52 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 51) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 51), hj2]
  have hj3 : (prorataWethVaultCodeChunk9.take 52) ++ ((prorataWethVaultCodeChunk9.drop 52).take 3) = prorataWethVaultCodeChunk9.take 55 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 52) (j := 3)).symm
  rw [hj3]

private theorem maxWithdrawStatic_1127_compile :
    Func.compile vaultTable 1127 (maxWithdrawStatic) = some (prorataWethVaultCodeChunk4.drop 103 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 59) := by
  rw [maxWithdrawStatic, compile_prepend, maxDepositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk4.drop 103).take 4 := by
    rw [maxDepositStaticPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk4.drop 111 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 55) : Bytes).length = 1224 := by decide +kernel
  have hbranch := compile_branch vaultTable 1131 2359 _ _
    (prorataWethVaultCodeChunk4.drop 111 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 55) [0x5f, 0x5f, 0xfd]
    maxWithdrawCanonical_1135_compile (by rw [hlen]) (by decide) (revert_compile_at 2360)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (2359 >>> 8).toUInt8, Nat.toUInt8 2359, 0x57] : Bytes) = (prorataWethVaultCodeChunk4.drop 107).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk9.drop 55).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk9.drop 56).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 103).take 4) ++ ((prorataWethVaultCodeChunk4.drop 107).take 4) = (prorataWethVaultCodeChunk4.drop 103).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4.drop 103) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 103).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk4.drop 103).take 8) ++ (prorataWethVaultCodeChunk4.drop 111) = prorataWethVaultCodeChunk4.drop 103 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk4.drop 103)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 103).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk9.take 55) ++ ((prorataWethVaultCodeChunk9.drop 55).take 1) = prorataWethVaultCodeChunk9.take 56 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 55) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 55), hj2]
  have hj3 : (prorataWethVaultCodeChunk9.take 56) ++ ((prorataWethVaultCodeChunk9.drop 56).take 3) = prorataWethVaultCodeChunk9.take 59 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 56) (j := 3)).symm
  rw [hj3]

private theorem maxWithdraw_source_cut : ProrataWethVault.routed 1 ProrataWethVault.maxWithdraw = nonpayable maxWithdrawStatic := by rfl
private theorem maxWithdraw_endpoint_compile :
    Func.compile vaultTable 1117 (ProrataWethVault.routed 1 ProrataWethVault.maxWithdraw) = some (prorataWethVaultCodeChunk4.drop 93 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 59) := by
  rw [maxWithdraw_source_cut]
  have hcut : nonpayable maxWithdrawStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert maxWithdrawStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 1119 1126 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk4.drop 103 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 59)
    (revert_compile_at 1123) (by rfl) (by decide) maxWithdrawStatic_1127_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (1126 >>> 8).toUInt8, Nat.toUInt8 1126, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk4.drop 93).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (1126 >>> 8).toUInt8, Nat.toUInt8 1126, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 93).take 10) ++ (prorataWethVaultCodeChunk4.drop 103) = prorataWethVaultCodeChunk4.drop 93 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk4.drop 93)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 93).take 10), hj0]

private theorem maxMintFinish_compile_at (n : Nat) :
    Func.compile vaultTable n (ProrataWethVault.finishQuotient .capDown ProrataWethVault.maxMintAfterAssetCapSlot) =
      some [0x61, 0x03, 0x00, 0x51, 0x61, 0x43, 0xe2, 0x56] := by
  simp only [ProrataWethVault.finishQuotient, ProrataWethVault.loadWord, prepend]
  simp only [Func.compile, vault_table_maxMintAfterAssetCap]
  rfl
private theorem maxMintCore_compile_at (n : Nat) :
    Func.compile vaultTable n (ProrataWethVault.divideWideCore .capDown ProrataWethVault.maxMintAfterAssetCapSlot) =
      some (wideCorePrefix.flatMap Ninst.toBytes ++ ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes ++
        wideCoreSuffix.flatMap Ninst.toBytes ++ [0x61, 0x03, 0x00, 0x51, 0x61, 0x43, 0xe2, 0x56]) := by
  exact divideWideCore_compile_from_finish n .capDown ProrataWethVault.maxMintAfterAssetCapSlot _
    (maxMintFinish_compile_at (n + 347))
private theorem maxMintWide_source_cut :
    ProrataWethVault.divideWide .capDown ProrataWethVault.maxMintAfterAssetCapSlot =
      wideGuardPrefix +++ Func.branch
        (ProrataWethVault.divisionOverflow .capDown ProrataWethVault.maxMintAfterAssetCapSlot)
        (ProrataWethVault.divideWideCore .capDown ProrataWethVault.maxMintAfterAssetCapSlot) := by rfl
private def maxMintNonzero : Func := highZeroPrefix +++ Func.branch
  (ProrataWethVault.divideWide .capDown ProrataWethVault.maxMintAfterAssetCapSlot)
  (ProrataWethVault.divideSimple .capDown ProrataWethVault.maxMintAfterAssetCapSlot)
private theorem maxMintDivide_source_cut :
    ProrataWethVault.divide512 .capDown ProrataWethVault.maxMintAfterAssetCapSlot =
      denominatorZeroPrefix +++ Func.branch maxMintNonzero Func.revert := by rfl

private theorem maxMintCore_3609_compile :
    Func.compile vaultTable 3609
      (ProrataWethVault.divideWideCore .capDown ProrataWethVault.maxMintAfterAssetCapSlot) =
      some (prorataWethVaultCodeChunk14.drop 25 ++ prorataWethVaultCodeChunk15.take 124) := by
  have hr : wideCoreRemainderPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk14.drop 25).take 117 := by rfl
  have hi : wideCoreInversePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk14.drop 142).take 91 := by rfl
  have hn : ProrataWethVault.sixNewtonSteps.flatMap Ninst.toBytes = prorataWethVaultCodeChunk14.drop 233 ++ prorataWethVaultCodeChunk15.take 103 := by
    let three : Line := ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep ++ ProrataWethVault.newtonStep
    have hsource : ProrataWethVault.sixNewtonSteps = three ++ three := by rfl
    have hfirst : three.flatMap Ninst.toBytes = prorataWethVaultCodeChunk14.drop 233 ++ prorataWethVaultCodeChunk15.take 40 := by rfl
    have hsecond : three.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk15.drop 40).take 63 := by rfl
    rw [hsource, List.flatMap_append]
    calc
      _ = _ ++ _ := congrArg₂ List.append hfirst hsecond
      _ = _ := by
        try simp only [List.append_assoc]
        have hj0 : (prorataWethVaultCodeChunk15.take 40) ++ ((prorataWethVaultCodeChunk15.drop 40).take 63) = prorataWethVaultCodeChunk15.take 103 := by
          simpa only [List.drop_drop, Nat.reduceAdd] using
            (List.take_add (l := prorataWethVaultCodeChunk15) (i := 40) (j := 63)).symm
        rw [hj0]
  have hs : wideCoreSuffix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk15.drop 103).take 13 := by rfl
  have hfinish : ([0x61, 0x03, 0x00, 0x51, 0x61, 0x43, 0xe2, 0x56] : Bytes) = (prorataWethVaultCodeChunk15.drop 116).take 8 := by rfl
  rw [maxMintCore_compile_at, wideCorePrefix, List.flatMap_append, hr, hi, hn, hs, hfinish]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk14.drop 25).take 117) ++ ((prorataWethVaultCodeChunk14.drop 142).take 91) = (prorataWethVaultCodeChunk14.drop 25).take 208 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk14.drop 25) (i := 117) (j := 91)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk14.drop 25).take 117), hj0]
  have hj1 : ((prorataWethVaultCodeChunk14.drop 25).take 208) ++ (prorataWethVaultCodeChunk14.drop 233) = prorataWethVaultCodeChunk14.drop 25 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 208 (prorataWethVaultCodeChunk14.drop 25)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk14.drop 25).take 208), hj1]
  have hj2 : (prorataWethVaultCodeChunk15.take 103) ++ ((prorataWethVaultCodeChunk15.drop 103).take 13) = prorataWethVaultCodeChunk15.take 116 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk15) (i := 103) (j := 13)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk15.take 103), hj2]
  have hj3 : (prorataWethVaultCodeChunk15.take 116) ++ ((prorataWethVaultCodeChunk15.drop 116).take 8) = prorataWethVaultCodeChunk15.take 124 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk15) (i := 116) (j := 8)).symm
  rw [hj3]

private theorem maxMintOverflow_3571_compile :
    Func.compile vaultTable 3571 (ProrataWethVault.divisionOverflow .capDown ProrataWethVault.maxMintAfterAssetCapSlot) =
      some (prorataWethVaultCodeChunk13.drop 243 ++ prorataWethVaultCodeChunk14.take 24) := by
  simp only [ProrataWethVault.divisionOverflow, Func.compile, vault_table_maxMintAfterAssetCap]
  rfl
private theorem maxMintSimple_3965_compile :
    Func.compile vaultTable 3965 (ProrataWethVault.divideSimple .capDown ProrataWethVault.maxMintAfterAssetCapSlot) =
      some ((prorataWethVaultCodeChunk15.drop 125).take 34) := by
  simp only [ProrataWethVault.divideSimple, ProrataWethVault.finishQuotient,
    ProrataWethVault.loadWord, mstoreAt, prepend]
  simp only [Func.compile, vault_table_maxMintAfterAssetCap]
  rfl

private theorem maxMintWide_3558_compile :
    Func.compile vaultTable 3558 (ProrataWethVault.divideWide .capDown ProrataWethVault.maxMintAfterAssetCapSlot) = some (prorataWethVaultCodeChunk13.drop 230 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 124) := by
  rw [maxMintWide_source_cut, compile_prepend, wideGuardPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : wideGuardPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 230).take 9 := by
    rw [wideGuardPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk13.drop 243 ++ prorataWethVaultCodeChunk14.take 24) : Bytes).length = 37 := by decide +kernel
  have hbranch := compile_branch vaultTable 3567 3608 _ _
    (prorataWethVaultCodeChunk13.drop 243 ++ prorataWethVaultCodeChunk14.take 24) (prorataWethVaultCodeChunk14.drop 25 ++ prorataWethVaultCodeChunk15.take 124)
    maxMintOverflow_3571_compile (by rw [hlen]) (by decide) maxMintCore_3609_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3608 >>> 8).toUInt8, Nat.toUInt8 3608, 0x57] : Bytes) = (prorataWethVaultCodeChunk13.drop 239).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk14.drop 24).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 230).take 9) ++ ((prorataWethVaultCodeChunk13.drop 239).take 4) = (prorataWethVaultCodeChunk13.drop 230).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk13.drop 230) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 230).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk13.drop 230).take 13) ++ (prorataWethVaultCodeChunk13.drop 243) = prorataWethVaultCodeChunk13.drop 230 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 13 (prorataWethVaultCodeChunk13.drop 230)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 230).take 13), hj1]
  have hj2 : (prorataWethVaultCodeChunk14.take 24) ++ ((prorataWethVaultCodeChunk14.drop 24).take 1) = prorataWethVaultCodeChunk14.take 25 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk14) (i := 24) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk14.take 24), hj2]
  have hj3 : (prorataWethVaultCodeChunk14.take 25) ++ (prorataWethVaultCodeChunk14.drop 25) = prorataWethVaultCodeChunk14 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 25 (prorataWethVaultCodeChunk14)
  rw [← List.append_assoc (prorataWethVaultCodeChunk14.take 25), hj3]

private theorem maxMintNonzero_3549_compile :
    Func.compile vaultTable 3549 (maxMintNonzero) = some (prorataWethVaultCodeChunk13.drop 221 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 159) := by
  rw [maxMintNonzero, compile_prepend, highZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : highZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 221).take 5 := by
    rw [highZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk13.drop 230 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 124) : Bytes).length = 406 := by decide +kernel
  have hbranch := compile_branch vaultTable 3554 3964 _ _
    (prorataWethVaultCodeChunk13.drop 230 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 124) ((prorataWethVaultCodeChunk15.drop 125).take 34)
    maxMintWide_3558_compile (by rw [hlen]) (by decide) maxMintSimple_3965_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3964 >>> 8).toUInt8, Nat.toUInt8 3964, 0x57] : Bytes) = (prorataWethVaultCodeChunk13.drop 226).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk15.drop 124).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 221).take 5) ++ ((prorataWethVaultCodeChunk13.drop 226).take 4) = (prorataWethVaultCodeChunk13.drop 221).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk13.drop 221) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 221).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk13.drop 221).take 9) ++ (prorataWethVaultCodeChunk13.drop 230) = prorataWethVaultCodeChunk13.drop 221 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk13.drop 221)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 221).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk15.take 124) ++ ((prorataWethVaultCodeChunk15.drop 124).take 1) = prorataWethVaultCodeChunk15.take 125 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk15) (i := 124) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk15.take 124), hj2]
  have hj3 : (prorataWethVaultCodeChunk15.take 125) ++ ((prorataWethVaultCodeChunk15.drop 125).take 34) = prorataWethVaultCodeChunk15.take 159 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk15) (i := 125) (j := 34)).symm
  rw [hj3]

private theorem maxMintDivide_3540_compile :
    Func.compile vaultTable 3540 (ProrataWethVault.divide512 .capDown ProrataWethVault.maxMintAfterAssetCapSlot) = some (prorataWethVaultCodeChunk13.drop 212 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 163) := by
  rw [maxMintDivide_source_cut, compile_prepend, denominatorZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : denominatorZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 212).take 5 := by
    rw [denominatorZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk13.drop 221 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 159) : Bytes).length = 450 := by decide +kernel
  have hbranch := compile_branch vaultTable 3545 3999 _ _
    (prorataWethVaultCodeChunk13.drop 221 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 159) [0x5f, 0x5f, 0xfd]
    maxMintNonzero_3549_compile (by rw [hlen]) (by decide) (revert_compile_at 4000)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (3999 >>> 8).toUInt8, Nat.toUInt8 3999, 0x57] : Bytes) = (prorataWethVaultCodeChunk13.drop 217).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk15.drop 159).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk15.drop 160).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 212).take 5) ++ ((prorataWethVaultCodeChunk13.drop 217).take 4) = (prorataWethVaultCodeChunk13.drop 212).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk13.drop 212) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 212).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk13.drop 212).take 9) ++ (prorataWethVaultCodeChunk13.drop 221) = prorataWethVaultCodeChunk13.drop 212 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk13.drop 212)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 212).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk15.take 159) ++ ((prorataWethVaultCodeChunk15.drop 159).take 1) = prorataWethVaultCodeChunk15.take 160 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk15) (i := 159) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk15.take 159), hj2]
  have hj3 : (prorataWethVaultCodeChunk15.take 160) ++ ((prorataWethVaultCodeChunk15.drop 160).take 3) = prorataWethVaultCodeChunk15.take 163 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk15) (i := 160) (j := 3)).symm
  rw [hj3]

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintMultiplyStage : Line := [Ninst.pushB256 B256.max] ++ mstoreAt xWord ++ stagedDenominator ++ mstoreAt yWord ++ loadWord xWord ++ loadWord yWord ++ [mul] ++ mstoreAt lowWord
private theorem maxMintMultiplyStage_size : prefixByteSize maxMintMultiplyStage = 62 := by rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintMulStage : Line := stagedAssetFactor ++ mstoreAt denominatorWord ++ maxMintMultiplyStage
private theorem maxMintMulStage_size : prefixByteSize maxMintMulStage = 73 := by rfl

open ProrataWethVault in
private theorem maxMintMul_source_cut : mulDiv [Ninst.pushB256 B256.max] stagedDenominator stagedAssetFactor .capDown maxMintAfterAssetCapSlot =
    maxMintMulStage +++ maxDepositMulRecover +++ divide512 .capDown maxMintAfterAssetCapSlot := by rfl
open ProrataWethVault in
private theorem maxMintProduct_source_cut : productOverTwoPow256 [Ninst.pushB256 B256.max] stagedDenominator .down maxMintAfterAssetCapSlot =
    maxMintMultiplyStage +++ maxDepositMulRecover +++ depositProductTail +++ finishQuotient .down maxMintAfterAssetCapSlot := by rfl
private theorem maxMintProductFinish_4167_compile :
    Func.compile vaultTable 4167 (ProrataWethVault.finishQuotient .down ProrataWethVault.maxMintAfterAssetCapSlot) =
      some ((prorataWethVaultCodeChunk16.drop 71).take 8) := by
  have hsource : ProrataWethVault.finishQuotient .down ProrataWethVault.maxMintAfterAssetCapSlot =
      ProrataWethVault.finishQuotient .capDown ProrataWethVault.maxMintAfterAssetCapSlot := by rfl
  rw [hsource, maxMintFinish_compile_at]
  rfl

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintArithmetic : Func := Func.branch (mulDiv [Ninst.pushB256 B256.max] stagedDenominator stagedAssetFactor .capDown maxMintAfterAssetCapSlot) (productOverTwoPow256 [Ninst.pushB256 B256.max] stagedDenominator .down maxMintAfterAssetCapSlot)

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintAssets : Func := maxDepositAssetsPrefix +++ maxMintArithmetic

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintReturnSize : Func := maxDepositReturnSizePrefix +++ Func.branch maxMintAssets Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintRead : Func := maxDepositReadPrefix +++ Func.branch maxMintReturnSize Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintSupply : Func := maxDepositSupplyPrefix +++ Func.branch maxMintRead (returnConstant 0)

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintZero : Func := maxDepositZeroPrefix +++ Func.branch maxMintSupply (returnConstant 0)

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintCanonical : Func := maxDepositCanonicalPrefix +++ Func.branch maxMintZero Func.revert

open ProrataWethVault Jaune.Ninst Ninst in
private def maxMintStatic : Func := maxDepositStaticPrefix +++ Func.branch maxMintCanonical Func.revert

open ProrataWethVault in
private theorem maxMintMul_3382_compile :
    Func.compile vaultTable 3382 (mulDiv [Ninst.pushB256 B256.max] stagedDenominator stagedAssetFactor .capDown maxMintAfterAssetCapSlot) = some (prorataWethVaultCodeChunk13.drop 54 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 163) := by
  have hb0 : maxMintMulStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 54).take 73 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 127).take 85 := by
    rfl
  rw [maxMintMul_source_cut]
  rw [compile_prepend, maxMintMulStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [maxMintDivide_3540_compile, hb0, hb1]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 54).take 73) ++ ((prorataWethVaultCodeChunk13.drop 127).take 85) = (prorataWethVaultCodeChunk13.drop 54).take 158 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk13.drop 54) (i := 73) (j := 85)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 54).take 73), hj0]
  have hj1 : ((prorataWethVaultCodeChunk13.drop 54).take 158) ++ (prorataWethVaultCodeChunk13.drop 212) = prorataWethVaultCodeChunk13.drop 54 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 158 (prorataWethVaultCodeChunk13.drop 54)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 54).take 158), hj1]

open ProrataWethVault in
private theorem maxMintProduct_4004_compile :
    Func.compile vaultTable 4004 (productOverTwoPow256 [Ninst.pushB256 B256.max] stagedDenominator .down maxMintAfterAssetCapSlot) = some (prorataWethVaultCodeChunk15.drop 164 ++ prorataWethVaultCodeChunk16.take 79) := by
  have hb0 : maxMintMultiplyStage.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk15.drop 164).take 62 := by
    rfl
  have hb1 : maxDepositMulRecover.flatMap Ninst.toBytes = prorataWethVaultCodeChunk15.drop 226 ++ prorataWethVaultCodeChunk16.take 55 := by
    rfl
  have hb2 : depositProductTail.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk16.drop 55).take 16 := by
    rfl
  rw [maxMintProduct_source_cut]
  rw [compile_prepend, maxMintMultiplyStage_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, maxDepositMulRecover_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [compile_prepend, depositProductTail_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [maxMintProductFinish_4167_compile, hb0, hb1, hb2]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk15.drop 164).take 62) ++ (prorataWethVaultCodeChunk15.drop 226) = prorataWethVaultCodeChunk15.drop 164 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 62 (prorataWethVaultCodeChunk15.drop 164)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk15.drop 164).take 62), hj0]
  have hj1 : (prorataWethVaultCodeChunk16.take 55) ++ ((prorataWethVaultCodeChunk16.drop 55).take 16) = prorataWethVaultCodeChunk16.take 71 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 55) (j := 16)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 55), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 71) ++ ((prorataWethVaultCodeChunk16.drop 71).take 8) = prorataWethVaultCodeChunk16.take 79 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 71) (j := 8)).symm
  rw [hj2]

private theorem maxMintArithmetic_3378_compile :
    Func.compile vaultTable 3378 (maxMintArithmetic) = some (prorataWethVaultCodeChunk13.drop 50 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 79) := by
  rw [maxMintArithmetic]
  have hlen : ((prorataWethVaultCodeChunk13.drop 54 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 163) : Bytes).length = 621 := by decide +kernel
  have hbranch := compile_branch vaultTable 3378 4003 _ _
    (prorataWethVaultCodeChunk13.drop 54 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15.take 163) (prorataWethVaultCodeChunk15.drop 164 ++ prorataWethVaultCodeChunk16.take 79)
    maxMintMul_3382_compile (by rw [hlen]) (by decide) maxMintProduct_4004_compile
  rw [hbranch]
  simp only [List.append_assoc]
  have hheader : ([0x61, (4003 >>> 8).toUInt8, Nat.toUInt8 4003, 0x57] : Bytes) = (prorataWethVaultCodeChunk13.drop 50).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk15.drop 163).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 50).take 4) ++ (prorataWethVaultCodeChunk13.drop 54) = prorataWethVaultCodeChunk13.drop 50 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 4 (prorataWethVaultCodeChunk13.drop 50)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 50).take 4), hj0]
  have hj1 : (prorataWethVaultCodeChunk15.take 163) ++ ((prorataWethVaultCodeChunk15.drop 163).take 1) = prorataWethVaultCodeChunk15.take 164 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk15) (i := 163) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk15.take 163), hj1]
  have hj2 : (prorataWethVaultCodeChunk15.take 164) ++ (prorataWethVaultCodeChunk15.drop 164) = prorataWethVaultCodeChunk15 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 164 (prorataWethVaultCodeChunk15)
  rw [← List.append_assoc (prorataWethVaultCodeChunk15.take 164), hj2]

private theorem maxMintAssets_3366_compile :
    Func.compile vaultTable 3366 (maxMintAssets) = some (prorataWethVaultCodeChunk13.drop 38 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 79) := by
  have hb0 : maxDepositAssetsPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 38).take 12 := by
    rw [maxDepositAssetsPrefix_bytes]
    rfl
  rw [maxMintAssets]
  rw [compile_prepend, maxDepositAssetsPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [maxMintArithmetic_3378_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 38).take 12) ++ (prorataWethVaultCodeChunk13.drop 50) = prorataWethVaultCodeChunk13.drop 38 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 12 (prorataWethVaultCodeChunk13.drop 38)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 38).take 12), hj0]

private theorem maxMintReturnSize_3357_compile :
    Func.compile vaultTable 3357 (maxMintReturnSize) = some (prorataWethVaultCodeChunk13.drop 29 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 83) := by
  rw [maxMintReturnSize, compile_prepend, maxDepositReturnSizePrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReturnSizePrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 29).take 5 := by
    rw [maxDepositReturnSizePrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk13.drop 38 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 79) : Bytes).length = 809 := by decide +kernel
  have hbranch := compile_branch vaultTable 3362 4175 _ _
    (prorataWethVaultCodeChunk13.drop 38 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 79) [0x5f, 0x5f, 0xfd]
    maxMintAssets_3366_compile (by rw [hlen]) (by decide) (revert_compile_at 4176)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4175 >>> 8).toUInt8, Nat.toUInt8 4175, 0x57] : Bytes) = (prorataWethVaultCodeChunk13.drop 34).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk16.drop 79).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk16.drop 80).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 29).take 5) ++ ((prorataWethVaultCodeChunk13.drop 34).take 4) = (prorataWethVaultCodeChunk13.drop 29).take 9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk13.drop 29) (i := 5) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 29).take 5), hj0]
  have hj1 : ((prorataWethVaultCodeChunk13.drop 29).take 9) ++ (prorataWethVaultCodeChunk13.drop 38) = prorataWethVaultCodeChunk13.drop 29 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 9 (prorataWethVaultCodeChunk13.drop 29)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 29).take 9), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 79) ++ ((prorataWethVaultCodeChunk16.drop 79).take 1) = prorataWethVaultCodeChunk16.take 80 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 79) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 79), hj2]
  have hj3 : (prorataWethVaultCodeChunk16.take 80) ++ ((prorataWethVaultCodeChunk16.drop 80).take 3) = prorataWethVaultCodeChunk16.take 83 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 80) (j := 3)).symm
  rw [hj3]

private theorem maxMintRead_3329_compile :
    Func.compile vaultTable 3329 (maxMintRead) = some (prorataWethVaultCodeChunk13.drop 1 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 87) := by
  rw [maxMintRead, compile_prepend, maxDepositReadPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositReadPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk13.drop 1).take 24 := by
    rw [maxDepositReadPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk13.drop 29 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 83) : Bytes).length = 822 := by decide +kernel
  have hbranch := compile_branch vaultTable 3353 4179 _ _
    (prorataWethVaultCodeChunk13.drop 29 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 83) [0x5f, 0x5f, 0xfd]
    maxMintReturnSize_3357_compile (by rw [hlen]) (by decide) (revert_compile_at 4180)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4179 >>> 8).toUInt8, Nat.toUInt8 4179, 0x57] : Bytes) = (prorataWethVaultCodeChunk13.drop 25).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk16.drop 83).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk16.drop 84).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk13.drop 1).take 24) ++ ((prorataWethVaultCodeChunk13.drop 25).take 4) = (prorataWethVaultCodeChunk13.drop 1).take 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk13.drop 1) (i := 24) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 1).take 24), hj0]
  have hj1 : ((prorataWethVaultCodeChunk13.drop 1).take 28) ++ (prorataWethVaultCodeChunk13.drop 29) = prorataWethVaultCodeChunk13.drop 1 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 28 (prorataWethVaultCodeChunk13.drop 1)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk13.drop 1).take 28), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 83) ++ ((prorataWethVaultCodeChunk16.drop 83).take 1) = prorataWethVaultCodeChunk16.take 84 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 83) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 83), hj2]
  have hj3 : (prorataWethVaultCodeChunk16.take 84) ++ ((prorataWethVaultCodeChunk16.drop 84).take 3) = prorataWethVaultCodeChunk16.take 87 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 84) (j := 3)).symm
  rw [hj3]

private theorem maxMintZero_4184_compile :
    Func.compile vaultTable 4184 (ProrataWethVault.returnConstant 0) = some ((prorataWethVaultCodeChunk16.drop 88).take 7) := by
  rw [returnConstant_zero_compile_at]
  rfl

private theorem maxMintSupply_3280_compile :
    Func.compile vaultTable 3280 (maxMintSupply) = some (prorataWethVaultCodeChunk12.drop 208 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 95) := by
  rw [maxMintSupply, compile_prepend, maxDepositSupplyPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositSupplyPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk12.drop 208).take 45 := by
    rw [maxDepositSupplyPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk13.drop 1 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 87) : Bytes).length = 854 := by decide +kernel
  have hbranch := compile_branch vaultTable 3325 4183 _ _
    (prorataWethVaultCodeChunk13.drop 1 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 87) ((prorataWethVaultCodeChunk16.drop 88).take 7)
    maxMintRead_3329_compile (by rw [hlen]) (by decide) maxMintZero_4184_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4183 >>> 8).toUInt8, Nat.toUInt8 4183, 0x57] : Bytes) = prorataWethVaultCodeChunk12.drop 253 ++ prorataWethVaultCodeChunk13.take 1 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk16.drop 87).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk12.drop 208).take 45) ++ (prorataWethVaultCodeChunk12.drop 253) = prorataWethVaultCodeChunk12.drop 208 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 45 (prorataWethVaultCodeChunk12.drop 208)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 208).take 45), hj0]
  have hj1 : (prorataWethVaultCodeChunk13.take 1) ++ (prorataWethVaultCodeChunk13.drop 1) = prorataWethVaultCodeChunk13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 1 (prorataWethVaultCodeChunk13)
  rw [← List.append_assoc (prorataWethVaultCodeChunk13.take 1), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 87) ++ ((prorataWethVaultCodeChunk16.drop 87).take 1) = prorataWethVaultCodeChunk16.take 88 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 87) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 87), hj2]
  have hj3 : (prorataWethVaultCodeChunk16.take 88) ++ ((prorataWethVaultCodeChunk16.drop 88).take 7) = prorataWethVaultCodeChunk16.take 95 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 88) (j := 7)).symm
  rw [hj3]

private theorem maxMintZero_4192_compile :
    Func.compile vaultTable 4192 (ProrataWethVault.returnConstant 0) = some ((prorataWethVaultCodeChunk16.drop 96).take 7) := by
  rw [returnConstant_zero_compile_at]
  rfl

private theorem maxMintZero_3272_compile :
    Func.compile vaultTable 3272 (maxMintZero) = some (prorataWethVaultCodeChunk12.drop 200 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 103) := by
  rw [maxMintZero, compile_prepend, maxDepositZeroPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositZeroPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk12.drop 200).take 4 := by
    rw [maxDepositZeroPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk12.drop 208 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 95) : Bytes).length = 911 := by decide +kernel
  have hbranch := compile_branch vaultTable 3276 4191 _ _
    (prorataWethVaultCodeChunk12.drop 208 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 95) ((prorataWethVaultCodeChunk16.drop 96).take 7)
    maxMintSupply_3280_compile (by rw [hlen]) (by decide) maxMintZero_4192_compile
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4191 >>> 8).toUInt8, Nat.toUInt8 4191, 0x57] : Bytes) = (prorataWethVaultCodeChunk12.drop 204).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk16.drop 95).take 1 := by rfl
  rw [hheader, hjump]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk12.drop 200).take 4) ++ ((prorataWethVaultCodeChunk12.drop 204).take 4) = (prorataWethVaultCodeChunk12.drop 200).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12.drop 200) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 200).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk12.drop 200).take 8) ++ (prorataWethVaultCodeChunk12.drop 208) = prorataWethVaultCodeChunk12.drop 200 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk12.drop 200)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 200).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 95) ++ ((prorataWethVaultCodeChunk16.drop 95).take 1) = prorataWethVaultCodeChunk16.take 96 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 95) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 95), hj2]
  have hj3 : (prorataWethVaultCodeChunk16.take 96) ++ ((prorataWethVaultCodeChunk16.drop 96).take 7) = prorataWethVaultCodeChunk16.take 103 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 96) (j := 7)).symm
  rw [hj3]

private theorem maxMintCanonical_3259_compile :
    Func.compile vaultTable 3259 (maxMintCanonical) = some (prorataWethVaultCodeChunk12.drop 187 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 107) := by
  rw [maxMintCanonical, compile_prepend, maxDepositCanonicalPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositCanonicalPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk12.drop 187).take 9 := by
    rw [maxDepositCanonicalPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk12.drop 200 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 103) : Bytes).length = 927 := by decide +kernel
  have hbranch := compile_branch vaultTable 3268 4199 _ _
    (prorataWethVaultCodeChunk12.drop 200 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 103) [0x5f, 0x5f, 0xfd]
    maxMintZero_3272_compile (by rw [hlen]) (by decide) (revert_compile_at 4200)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4199 >>> 8).toUInt8, Nat.toUInt8 4199, 0x57] : Bytes) = (prorataWethVaultCodeChunk12.drop 196).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk16.drop 103).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk16.drop 104).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk12.drop 187).take 9) ++ ((prorataWethVaultCodeChunk12.drop 196).take 4) = (prorataWethVaultCodeChunk12.drop 187).take 13 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12.drop 187) (i := 9) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 187).take 9), hj0]
  have hj1 : ((prorataWethVaultCodeChunk12.drop 187).take 13) ++ (prorataWethVaultCodeChunk12.drop 200) = prorataWethVaultCodeChunk12.drop 187 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 13 (prorataWethVaultCodeChunk12.drop 187)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 187).take 13), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 103) ++ ((prorataWethVaultCodeChunk16.drop 103).take 1) = prorataWethVaultCodeChunk16.take 104 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 103) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 103), hj2]
  have hj3 : (prorataWethVaultCodeChunk16.take 104) ++ ((prorataWethVaultCodeChunk16.drop 104).take 3) = prorataWethVaultCodeChunk16.take 107 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 104) (j := 3)).symm
  rw [hj3]

private theorem maxMintStatic_3251_compile :
    Func.compile vaultTable 3251 (maxMintStatic) = some (prorataWethVaultCodeChunk12.drop 179 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111) := by
  rw [maxMintStatic, compile_prepend, maxDepositStaticPrefix_size]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  have hbytes : maxDepositStaticPrefix.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk12.drop 179).take 4 := by
    rw [maxDepositStaticPrefix_bytes]
    rfl
  have hlen : ((prorataWethVaultCodeChunk12.drop 187 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 107) : Bytes).length = 944 := by decide +kernel
  have hbranch := compile_branch vaultTable 3255 4203 _ _
    (prorataWethVaultCodeChunk12.drop 187 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 107) [0x5f, 0x5f, 0xfd]
    maxMintCanonical_3259_compile (by rw [hlen]) (by decide) (revert_compile_at 4204)
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hheader : ([0x61, (4203 >>> 8).toUInt8, Nat.toUInt8 4203, 0x57] : Bytes) = (prorataWethVaultCodeChunk12.drop 183).take 4 := by rfl
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk16.drop 107).take 1 := by rfl
  rw [hheader, hjump]
  have hqbytes : ([0x5f, 0x5f, 0xfd] : Bytes) = (prorataWethVaultCodeChunk16.drop 108).take 3 := by rfl
  rw [hqbytes]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk12.drop 179).take 4) ++ ((prorataWethVaultCodeChunk12.drop 183).take 4) = (prorataWethVaultCodeChunk12.drop 179).take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12.drop 179) (i := 4) (j := 4)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 179).take 4), hj0]
  have hj1 : ((prorataWethVaultCodeChunk12.drop 179).take 8) ++ (prorataWethVaultCodeChunk12.drop 187) = prorataWethVaultCodeChunk12.drop 179 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk12.drop 179)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 179).take 8), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 107) ++ ((prorataWethVaultCodeChunk16.drop 107).take 1) = prorataWethVaultCodeChunk16.take 108 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 107) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 107), hj2]
  have hj3 : (prorataWethVaultCodeChunk16.take 108) ++ ((prorataWethVaultCodeChunk16.drop 108).take 3) = prorataWethVaultCodeChunk16.take 111 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 108) (j := 3)).symm
  rw [hj3]

private theorem maxMint_source_cut : ProrataWethVault.routed 1 ProrataWethVault.maxMint = nonpayable maxMintStatic := by rfl
private theorem maxMint_endpoint_compile :
    Func.compile vaultTable 3241 (ProrataWethVault.routed 1 ProrataWethVault.maxMint) = some (prorataWethVaultCodeChunk12.drop 169 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111) := by
  rw [maxMint_source_cut]
  have hcut : nonpayable maxMintStatic =
      ([Ninst.callvalue, Ninst.iszero] : Line) +++ Func.branch Func.revert maxMintStatic := by rfl
  rw [hcut, compile_prepend]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.callvalue, Ninst.iszero] = 2 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 3243 3250 _ _
    [0x5f, 0x5f, 0xfd] (prorataWethVaultCodeChunk12.drop 179 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111)
    (revert_compile_at 3247) (by rfl) (by decide) maxMintStatic_3251_compile
  have hbytes : ([Ninst.callvalue, Ninst.iszero] : Line).flatMap Ninst.toBytes = [0x34, 0x15] := by rfl
  rw [hbranch, hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x34, 0x15] : Bytes) ++
      ([0x61, (3250 >>> 8).toUInt8, Nat.toUInt8 3250, 0x57] : Bytes) ++
      [0x5f, 0x5f, 0xfd] ++ [0x5b] = (prorataWethVaultCodeChunk12.drop 169).take 10 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x5f, 0x5f, 0xfd] : Bytes),
    ← List.append_assoc ([0x61, (3250 >>> 8).toUInt8, Nat.toUInt8 3250, 0x57] : Bytes),
    ← List.append_assoc ([0x34, 0x15] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk12.drop 169).take 10) ++ (prorataWethVaultCodeChunk12.drop 179) = prorataWethVaultCodeChunk12.drop 169 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 10 (prorataWethVaultCodeChunk12.drop 169)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 169).take 10), hj0]

private theorem mintSelector_value : selector "mint" [.uint256, .address] = (0x94bf804d : B256) := by decide +kernel

private theorem symbolSelector_value : selector "symbol" [] = (0x95d89b41 : B256) := by decide +kernel

private theorem transferSelector_value : selector "transfer" [.address, .uint256] = (0xa9059cbb : B256) := by decide +kernel

private theorem previewMintSelector_value : selector "previewMint" [.uint256] = (0xb3d7f6b9 : B256) := by decide +kernel

private theorem withdrawSelector_value : selector "withdraw" [.uint256, .address, .address] = (0xb460af94 : B256) := by decide +kernel

private theorem redeemSelector_value : selector "redeem" [.uint256, .address, .address] = (0xba087652 : B256) := by decide +kernel

private theorem maxMintSelector_value : selector "maxMint" [.address] = (0xc63d75b6 : B256) := by decide +kernel

private theorem convertToSharesSelector_value : selector "convertToShares" [.uint256] = (0xc6e6f592 : B256) := by decide +kernel

private theorem maxWithdrawSelector_value : selector "maxWithdraw" [.address] = (0xce96cb77 : B256) := by decide +kernel

private theorem mint_dispatch_compile :
    Func.compile vaultTable 7872 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftAPair.take 1))) = some (prorataWethVaultCodeChunk30.drop 192 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) := by
  rw [mint_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "mint" [.uint256, .address]) (ProrataWethVault.routed 2 ProrataWethVault.mint)) =
      ([Ninst.pushB256 (selector "mint" [.uint256, .address]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 2 ProrataWethVault.mint) := by rfl
  rw [hcut, compile_prepend, mintSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0x94bf804d, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 7878 7886 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk30.drop 207 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218)
    (revert_slot_compile_at 7882) (by rfl) (by decide) mint_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0x94bf804d, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0x94, 0xbf, 0x80, 0x4d, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0x94, 0xbf, 0x80, 0x4d, 0x14] : Bytes) ++
      ([0x61, (7886 >>> 8).toUInt8, Nat.toUInt8 7886, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk30.drop 192).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (7886 >>> 8).toUInt8, Nat.toUInt8 7886, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0x94, 0xbf, 0x80, 0x4d, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 192).take 15) ++ (prorataWethVaultCodeChunk30.drop 207) = prorataWethVaultCodeChunk30.drop 192 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk30.drop 192)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 192).take 15), hj0]

private theorem symbol_dispatch_compile :
    Func.compile vaultTable 7808 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftAPair.drop 1))) = some ((prorataWethVaultCodeChunk30.drop 128).take 63) := by
  rw [symbol_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "symbol" []) (ProrataWethVault.routed 0 ProrataWethVault.symbol)) =
      ([Ninst.pushB256 (selector "symbol" []), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 0 ProrataWethVault.symbol) := by rfl
  rw [hcut, compile_prepend, symbolSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0x95d89b41, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 7814 7822 _ _
    [0x61, 0x3d, 0x2f, 0x56] ((prorataWethVaultCodeChunk30.drop 143).take 48)
    (revert_slot_compile_at 7818) (by rfl) (by decide) symbol_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0x95d89b41, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0x95, 0xd8, 0x9b, 0x41, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0x95, 0xd8, 0x9b, 0x41, 0x14] : Bytes) ++
      ([0x61, (7822 >>> 8).toUInt8, Nat.toUInt8 7822, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk30.drop 128).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (7822 >>> 8).toUInt8, Nat.toUInt8 7822, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0x95, 0xd8, 0x9b, 0x41, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 128).take 15) ++ ((prorataWethVaultCodeChunk30.drop 143).take 48) = (prorataWethVaultCodeChunk30.drop 128).take 63 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 128) (i := 15) (j := 48)).symm
  rw [hj0]

private theorem transfer_dispatch_compile :
    Func.compile vaultTable 7699 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightLeftA.drop 2))) = some ((prorataWethVaultCodeChunk30.drop 19).take 97) := by
  rw [transfer_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "transfer" [.address, .uint256]) (ProrataWethVault.routed 2 ProrataWethVault.transfer)) =
      ([Ninst.pushB256 (selector "transfer" [.address, .uint256]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 2 ProrataWethVault.transfer) := by rfl
  rw [hcut, compile_prepend, transferSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xa9059cbb, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 7705 7713 _ _
    [0x61, 0x3d, 0x2f, 0x56] ((prorataWethVaultCodeChunk30.drop 34).take 82)
    (revert_slot_compile_at 7709) (by rfl) (by decide) transfer_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xa9059cbb, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xa9, 0x5, 0x9c, 0xbb, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xa9, 0x5, 0x9c, 0xbb, 0x14] : Bytes) ++
      ([0x61, (7713 >>> 8).toUInt8, Nat.toUInt8 7713, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk30.drop 19).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (7713 >>> 8).toUInt8, Nat.toUInt8 7713, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xa9, 0x5, 0x9c, 0xbb, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 19).take 15) ++ ((prorataWethVaultCodeChunk30.drop 34).take 82) = (prorataWethVaultCodeChunk30.drop 19).take 97 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 19) (i := 15) (j := 82)).symm
  rw [hj0]

private theorem previewMint_dispatch_compile :
    Func.compile vaultTable 6397 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftBPair.take 1))) = some (prorataWethVaultCodeChunk24.drop 253 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7) := by
  rw [previewMint_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "previewMint" [.uint256]) (ProrataWethVault.routed 1 ProrataWethVault.previewMint)) =
      ([Ninst.pushB256 (selector "previewMint" [.uint256]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 1 ProrataWethVault.previewMint) := by rfl
  rw [hcut, compile_prepend, previewMintSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xb3d7f6b9, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 6403 6411 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk25.drop 12 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7)
    (revert_slot_compile_at 6407) (by rfl) (by decide) previewMint_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xb3d7f6b9, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xb3, 0xd7, 0xf6, 0xb9, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xb3, 0xd7, 0xf6, 0xb9, 0x14] : Bytes) ++
      ([0x61, (6411 >>> 8).toUInt8, Nat.toUInt8 6411, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = prorataWethVaultCodeChunk24.drop 253 ++ prorataWethVaultCodeChunk25.take 12 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (6411 >>> 8).toUInt8, Nat.toUInt8 6411, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xb3, 0xd7, 0xf6, 0xb9, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : (prorataWethVaultCodeChunk25.take 12) ++ (prorataWethVaultCodeChunk25.drop 12) = prorataWethVaultCodeChunk25 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 12 (prorataWethVaultCodeChunk25)
  rw [← List.append_assoc (prorataWethVaultCodeChunk25.take 12), hj0]

private theorem withdraw_dispatch_compile :
    Func.compile vaultTable 5427 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftBPair.drop 1))) = some (prorataWethVaultCodeChunk21.drop 51 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 252) := by
  rw [withdraw_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "withdraw" [.uint256, .address, .address]) (ProrataWethVault.routed 3 ProrataWethVault.withdraw)) =
      ([Ninst.pushB256 (selector "withdraw" [.uint256, .address, .address]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 3 ProrataWethVault.withdraw) := by rfl
  rw [hcut, compile_prepend, withdrawSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xb460af94, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 5433 5441 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk21.drop 66 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 252)
    (revert_slot_compile_at 5437) (by rfl) (by decide) withdraw_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xb460af94, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xb4, 0x60, 0xaf, 0x94, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xb4, 0x60, 0xaf, 0x94, 0x14] : Bytes) ++
      ([0x61, (5441 >>> 8).toUInt8, Nat.toUInt8 5441, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk21.drop 51).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (5441 >>> 8).toUInt8, Nat.toUInt8 5441, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xb4, 0x60, 0xaf, 0x94, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 51).take 15) ++ (prorataWethVaultCodeChunk21.drop 66) = prorataWethVaultCodeChunk21.drop 51 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk21.drop 51)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 51).take 15), hj0]

private theorem redeem_dispatch_compile :
    Func.compile vaultTable 4230 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightLeftB.drop 2))) = some (prorataWethVaultCodeChunk16.drop 134 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 39) := by
  rw [redeem_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "redeem" [.uint256, .address, .address]) (ProrataWethVault.routed 3 ProrataWethVault.redeem)) =
      ([Ninst.pushB256 (selector "redeem" [.uint256, .address, .address]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 3 ProrataWethVault.redeem) := by rfl
  rw [hcut, compile_prepend, redeemSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xba087652, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 4236 4244 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk16.drop 149 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 39)
    (revert_slot_compile_at 4240) (by rfl) (by decide) redeem_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xba087652, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xba, 0x8, 0x76, 0x52, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xba, 0x8, 0x76, 0x52, 0x14] : Bytes) ++
      ([0x61, (4244 >>> 8).toUInt8, Nat.toUInt8 4244, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk16.drop 134).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (4244 >>> 8).toUInt8, Nat.toUInt8 4244, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xba, 0x8, 0x76, 0x52, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 134).take 15) ++ (prorataWethVaultCodeChunk16.drop 149) = prorataWethVaultCodeChunk16.drop 134 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk16.drop 134)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 134).take 15), hj0]

private theorem maxMint_dispatch_compile :
    Func.compile vaultTable 3226 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightAPair.take 1))) = some (prorataWethVaultCodeChunk12.drop 154 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111) := by
  rw [maxMint_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "maxMint" [.address]) (ProrataWethVault.routed 1 ProrataWethVault.maxMint)) =
      ([Ninst.pushB256 (selector "maxMint" [.address]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 1 ProrataWethVault.maxMint) := by rfl
  rw [hcut, compile_prepend, maxMintSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xc63d75b6, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 3232 3240 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk12.drop 169 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111)
    (revert_slot_compile_at 3236) (by rfl) (by decide) maxMint_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xc63d75b6, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xc6, 0x3d, 0x75, 0xb6, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xc6, 0x3d, 0x75, 0xb6, 0x14] : Bytes) ++
      ([0x61, (3240 >>> 8).toUInt8, Nat.toUInt8 3240, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk12.drop 154).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (3240 >>> 8).toUInt8, Nat.toUInt8 3240, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xc6, 0x3d, 0x75, 0xb6, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk12.drop 154).take 15) ++ (prorataWethVaultCodeChunk12.drop 169) = prorataWethVaultCodeChunk12.drop 154 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk12.drop 154)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk12.drop 154).take 15), hj0]

private theorem convertToShares_dispatch_compile :
    Func.compile vaultTable 2375 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightAPair.drop 1))) = some (prorataWethVaultCodeChunk9.drop 71 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 153) := by
  rw [convertToShares_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "convertToShares" [.uint256]) (ProrataWethVault.routed 1 ProrataWethVault.convertToShares)) =
      ([Ninst.pushB256 (selector "convertToShares" [.uint256]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 1 ProrataWethVault.convertToShares) := by rfl
  rw [hcut, compile_prepend, convertToSharesSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xc6e6f592, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 2381 2389 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk9.drop 86 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 153)
    (revert_slot_compile_at 2385) (by rfl) (by decide) convertToShares_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xc6e6f592, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xc6, 0xe6, 0xf5, 0x92, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xc6, 0xe6, 0xf5, 0x92, 0x14] : Bytes) ++
      ([0x61, (2389 >>> 8).toUInt8, Nat.toUInt8 2389, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk9.drop 71).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (2389 >>> 8).toUInt8, Nat.toUInt8 2389, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xc6, 0xe6, 0xf5, 0x92, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 71).take 15) ++ (prorataWethVaultCodeChunk9.drop 86) = prorataWethVaultCodeChunk9.drop 71 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk9.drop 71)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 71).take 15), hj0]

private theorem maxWithdraw_dispatch_compile :
    Func.compile vaultTable 1102 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightRightA.drop 2))) = some (prorataWethVaultCodeChunk4.drop 78 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 59) := by
  rw [maxWithdraw_leaf_source]
  have hcut : dispatchWith ProrataWethVault.revertSlot (.leaf (selector "maxWithdraw" [.address]) (ProrataWethVault.routed 1 ProrataWethVault.maxWithdraw)) =
      ([Ninst.pushB256 (selector "maxWithdraw" [.address]), Ninst.eq] : Line) +++
        Func.branch (Func.call ProrataWethVault.revertSlot) (ProrataWethVault.routed 1 ProrataWethVault.maxWithdraw) := by rfl
  rw [hcut, compile_prepend, maxWithdrawSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.pushB256 0xce96cb77, Ninst.eq] = 6 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hbranch := compile_branch vaultTable 1108 1116 _ _
    [0x61, 0x3d, 0x2f, 0x56] (prorataWethVaultCodeChunk4.drop 93 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 59)
    (revert_slot_compile_at 1112) (by rfl) (by decide) maxWithdraw_endpoint_compile
  rw [hbranch]
  have hbytes : ([Ninst.pushB256 0xce96cb77, Ninst.eq] : Line).flatMap Ninst.toBytes = [0x63, 0xce, 0x96, 0xcb, 0x77, 0x14] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hprefix : ([0x63, 0xce, 0x96, 0xcb, 0x77, 0x14] : Bytes) ++
      ([0x61, (1116 >>> 8).toUInt8, Nat.toUInt8 1116, 0x57] : Bytes) ++
      [0x61, 0x3d, 0x2f, 0x56] ++ [0x5b] = (prorataWethVaultCodeChunk4.drop 78).take 15 := by rfl
  simp only [List.append_assoc] at hprefix
  rw [← List.append_assoc ([0x61, 0x3d, 0x2f, 0x56] : Bytes),
    ← List.append_assoc ([0x61, (1116 >>> 8).toUInt8, Nat.toUInt8 1116, 0x57] : Bytes),
    ← List.append_assoc ([0x63, 0xce, 0x96, 0xcb, 0x77, 0x14] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 78).take 15) ++ (prorataWethVaultCodeChunk4.drop 93) = prorataWethVaultCodeChunk4.drop 78 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 15 (prorataWethVaultCodeChunk4.drop 78)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 78).take 15), hj0]

private theorem rootRightLeftAPair_dispatch_compile :
    Func.compile vaultTable 7797 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightLeftAPair)) = some (prorataWethVaultCodeChunk30.drop 117 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) := by
  rw [rootRightLeftAPair_dispatch_node]
  have hcut : dispatchNode (selector "symbol" []) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftAPair.take 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftAPair.drop 1))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "symbol" []), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftAPair.drop 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftAPair.take 1))) := by rfl
  rw [hcut, compile_prepend, symbolSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0x95d89b41, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : ((prorataWethVaultCodeChunk30.drop 128).take 63).length = 63 := by decide +kernel
  have hbranch := compile_branch vaultTable 7804 7871 _ _
    ((prorataWethVaultCodeChunk30.drop 128).take 63) (prorataWethVaultCodeChunk30.drop 192 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218)
    symbol_dispatch_compile (by rw [hlen]) (by decide) mint_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0x95d89b41, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0x95, 0xd8, 0x9b, 0x41, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 191).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0x95, 0xd8, 0x9b, 0x41, 0x11] : Bytes) ++
      ([0x61, (7871 >>> 8).toUInt8, Nat.toUInt8 7871, 0x57] : Bytes) = (prorataWethVaultCodeChunk30.drop 117).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0x95, 0xd8, 0x9b, 0x41, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 117).take 11) ++ ((prorataWethVaultCodeChunk30.drop 128).take 63) = (prorataWethVaultCodeChunk30.drop 117).take 74 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 117) (i := 11) (j := 63)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 117).take 11), hj0]
  have hj1 : ((prorataWethVaultCodeChunk30.drop 117).take 74) ++ ((prorataWethVaultCodeChunk30.drop 191).take 1) = (prorataWethVaultCodeChunk30.drop 117).take 75 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 117) (i := 74) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 117).take 74), hj1]
  have hj2 : ((prorataWethVaultCodeChunk30.drop 117).take 75) ++ (prorataWethVaultCodeChunk30.drop 192) = prorataWethVaultCodeChunk30.drop 117 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 75 (prorataWethVaultCodeChunk30.drop 117)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 117).take 75), hj2]

private theorem rootRightLeftA_dispatch_compile :
    Func.compile vaultTable 7688 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightLeftA)) = some (prorataWethVaultCodeChunk30.drop 8 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) := by
  rw [rootRightLeftA_dispatch_node]
  have hcut : dispatchNode (selector "transfer" [.address, .uint256]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightLeftAPair)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightLeftA.drop 2))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "transfer" [.address, .uint256]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightLeftA.drop 2))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightLeftAPair)) := by rfl
  rw [hcut, compile_prepend, transferSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xa9059cbb, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : ((prorataWethVaultCodeChunk30.drop 19).take 97).length = 97 := by decide +kernel
  have hbranch := compile_branch vaultTable 7695 7796 _ _
    ((prorataWethVaultCodeChunk30.drop 19).take 97) (prorataWethVaultCodeChunk30.drop 117 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218)
    transfer_dispatch_compile (by rw [hlen]) (by decide) rootRightLeftAPair_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xa9059cbb, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xa9, 0x5, 0x9c, 0xbb, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 116).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xa9, 0x5, 0x9c, 0xbb, 0x11] : Bytes) ++
      ([0x61, (7796 >>> 8).toUInt8, Nat.toUInt8 7796, 0x57] : Bytes) = (prorataWethVaultCodeChunk30.drop 8).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xa9, 0x5, 0x9c, 0xbb, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk30.drop 8).take 11) ++ ((prorataWethVaultCodeChunk30.drop 19).take 97) = (prorataWethVaultCodeChunk30.drop 8).take 108 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 8) (i := 11) (j := 97)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 8).take 11), hj0]
  have hj1 : ((prorataWethVaultCodeChunk30.drop 8).take 108) ++ ((prorataWethVaultCodeChunk30.drop 116).take 1) = (prorataWethVaultCodeChunk30.drop 8).take 109 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30.drop 8) (i := 108) (j := 1)).symm
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 8).take 108), hj1]
  have hj2 : ((prorataWethVaultCodeChunk30.drop 8).take 109) ++ (prorataWethVaultCodeChunk30.drop 117) = prorataWethVaultCodeChunk30.drop 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 109 (prorataWethVaultCodeChunk30.drop 8)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk30.drop 8).take 109), hj2]

private theorem rootRightLeftBPair_dispatch_compile :
    Func.compile vaultTable 5416 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightLeftBPair)) = some (prorataWethVaultCodeChunk21.drop 40 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7) := by
  rw [rootRightLeftBPair_dispatch_node]
  have hcut : dispatchNode (selector "withdraw" [.uint256, .address, .address]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftBPair.take 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftBPair.drop 1))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "withdraw" [.uint256, .address, .address]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftBPair.drop 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightLeftBPair.take 1))) := by rfl
  rw [hcut, compile_prepend, withdrawSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xb460af94, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk21.drop 51 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 252).length = 969 := by decide +kernel
  have hbranch := compile_branch vaultTable 5423 6396 _ _
    (prorataWethVaultCodeChunk21.drop 51 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24.take 252) (prorataWethVaultCodeChunk24.drop 253 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7)
    withdraw_dispatch_compile (by rw [hlen]) (by decide) previewMint_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xb460af94, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xb4, 0x60, 0xaf, 0x94, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk24.drop 252).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xb4, 0x60, 0xaf, 0x94, 0x11] : Bytes) ++
      ([0x61, (6396 >>> 8).toUInt8, Nat.toUInt8 6396, 0x57] : Bytes) = (prorataWethVaultCodeChunk21.drop 40).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xb4, 0x60, 0xaf, 0x94, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk21.drop 40).take 11) ++ (prorataWethVaultCodeChunk21.drop 51) = prorataWethVaultCodeChunk21.drop 40 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk21.drop 40)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk21.drop 40).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk24.take 252) ++ ((prorataWethVaultCodeChunk24.drop 252).take 1) = prorataWethVaultCodeChunk24.take 253 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk24) (i := 252) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 252), hj1]
  have hj2 : (prorataWethVaultCodeChunk24.take 253) ++ (prorataWethVaultCodeChunk24.drop 253) = prorataWethVaultCodeChunk24 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 253 (prorataWethVaultCodeChunk24)
  rw [← List.append_assoc (prorataWethVaultCodeChunk24.take 253), hj2]

private theorem rootRightLeftB_dispatch_compile :
    Func.compile vaultTable 4219 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightLeftB)) = some (prorataWethVaultCodeChunk16.drop 123 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7) := by
  rw [rootRightLeftB_dispatch_node]
  have hcut : dispatchNode (selector "redeem" [.uint256, .address, .address]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightLeftBPair)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightLeftB.drop 2))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "redeem" [.uint256, .address, .address]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightLeftB.drop 2))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightLeftBPair)) := by rfl
  rw [hcut, compile_prepend, redeemSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xba087652, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk16.drop 134 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 39).length = 1185 := by decide +kernel
  have hbranch := compile_branch vaultTable 4226 5415 _ _
    (prorataWethVaultCodeChunk16.drop 134 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21.take 39) (prorataWethVaultCodeChunk21.drop 40 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7)
    redeem_dispatch_compile (by rw [hlen]) (by decide) rootRightLeftBPair_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xba087652, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xba, 0x8, 0x76, 0x52, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk21.drop 39).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xba, 0x8, 0x76, 0x52, 0x11] : Bytes) ++
      ([0x61, (5415 >>> 8).toUInt8, Nat.toUInt8 5415, 0x57] : Bytes) = (prorataWethVaultCodeChunk16.drop 123).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xba, 0x8, 0x76, 0x52, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 123).take 11) ++ (prorataWethVaultCodeChunk16.drop 134) = prorataWethVaultCodeChunk16.drop 123 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk16.drop 123)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 123).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk21.take 39) ++ ((prorataWethVaultCodeChunk21.drop 39).take 1) = prorataWethVaultCodeChunk21.take 40 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk21) (i := 39) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk21.take 39), hj1]
  have hj2 : (prorataWethVaultCodeChunk21.take 40) ++ (prorataWethVaultCodeChunk21.drop 40) = prorataWethVaultCodeChunk21 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 40 (prorataWethVaultCodeChunk21)
  rw [← List.append_assoc (prorataWethVaultCodeChunk21.take 40), hj2]

private theorem rootRightLeft_dispatch_compile :
    Func.compile vaultTable 4208 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 23 rootRightLeft)) = some (prorataWethVaultCodeChunk16.drop 112 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) := by
  rw [rootRightLeft_dispatch_node]
  have hcut : dispatchNode (selector "previewMint" [.uint256]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightLeftA)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightLeftB)) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "previewMint" [.uint256]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightLeftB)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightLeftA)) := by rfl
  rw [hcut, compile_prepend, previewMintSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xb3d7f6b9, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk16.drop 123 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7).length = 3468 := by decide +kernel
  have hbranch := compile_branch vaultTable 4215 7687 _ _
    (prorataWethVaultCodeChunk16.drop 123 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30.take 7) (prorataWethVaultCodeChunk30.drop 8 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218)
    rootRightLeftB_dispatch_compile (by rw [hlen]) (by decide) rootRightLeftA_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xb3d7f6b9, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xb3, 0xd7, 0xf6, 0xb9, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk30.drop 7).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xb3, 0xd7, 0xf6, 0xb9, 0x11] : Bytes) ++
      ([0x61, (7687 >>> 8).toUInt8, Nat.toUInt8 7687, 0x57] : Bytes) = (prorataWethVaultCodeChunk16.drop 112).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xb3, 0xd7, 0xf6, 0xb9, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk16.drop 112).take 11) ++ (prorataWethVaultCodeChunk16.drop 123) = prorataWethVaultCodeChunk16.drop 112 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk16.drop 112)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk16.drop 112).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk30.take 7) ++ ((prorataWethVaultCodeChunk30.drop 7).take 1) = prorataWethVaultCodeChunk30.take 8 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk30) (i := 7) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk30.take 7), hj1]
  have hj2 : (prorataWethVaultCodeChunk30.take 8) ++ (prorataWethVaultCodeChunk30.drop 8) = prorataWethVaultCodeChunk30 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 8 (prorataWethVaultCodeChunk30)
  rw [← List.append_assoc (prorataWethVaultCodeChunk30.take 8), hj2]

private theorem rootRightRightAPair_dispatch_compile :
    Func.compile vaultTable 2364 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightRightAPair)) = some (prorataWethVaultCodeChunk9.drop 60 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111) := by
  rw [rootRightRightAPair_dispatch_node]
  have hcut : dispatchNode (selector "convertToShares" [.uint256]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightAPair.take 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightAPair.drop 1))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "convertToShares" [.uint256]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightAPair.drop 1))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 20 (rootRightRightAPair.take 1))) := by rfl
  rw [hcut, compile_prepend, convertToSharesSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xc6e6f592, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk9.drop 71 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 153).length = 850 := by decide +kernel
  have hbranch := compile_branch vaultTable 2371 3225 _ _
    (prorataWethVaultCodeChunk9.drop 71 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12.take 153) (prorataWethVaultCodeChunk12.drop 154 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111)
    convertToShares_dispatch_compile (by rw [hlen]) (by decide) maxMint_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xc6e6f592, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xc6, 0xe6, 0xf5, 0x92, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk12.drop 153).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xc6, 0xe6, 0xf5, 0x92, 0x11] : Bytes) ++
      ([0x61, (3225 >>> 8).toUInt8, Nat.toUInt8 3225, 0x57] : Bytes) = (prorataWethVaultCodeChunk9.drop 60).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xc6, 0xe6, 0xf5, 0x92, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk9.drop 60).take 11) ++ (prorataWethVaultCodeChunk9.drop 71) = prorataWethVaultCodeChunk9.drop 60 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk9.drop 60)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk9.drop 60).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk12.take 153) ++ ((prorataWethVaultCodeChunk12.drop 153).take 1) = prorataWethVaultCodeChunk12.take 154 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk12) (i := 153) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 153), hj1]
  have hj2 : (prorataWethVaultCodeChunk12.take 154) ++ (prorataWethVaultCodeChunk12.drop 154) = prorataWethVaultCodeChunk12 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 154 (prorataWethVaultCodeChunk12)
  rw [← List.append_assoc (prorataWethVaultCodeChunk12.take 154), hj2]

private theorem rootRightRightA_dispatch_compile :
    Func.compile vaultTable 1091 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightRightA)) = some (prorataWethVaultCodeChunk4.drop 67 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111) := by
  rw [rootRightRightA_dispatch_node]
  have hcut : dispatchNode (selector "maxWithdraw" [.address]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightRightAPair)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightRightA.drop 2))) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "maxWithdraw" [.address]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 (rootRightRightA.drop 2))) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 21 rootRightRightAPair)) := by rfl
  rw [hcut, compile_prepend, maxWithdrawSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xce96cb77, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk4.drop 78 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 59).length = 1261 := by decide +kernel
  have hbranch := compile_branch vaultTable 1098 2363 _ _
    (prorataWethVaultCodeChunk4.drop 78 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9.take 59) (prorataWethVaultCodeChunk9.drop 60 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111)
    maxWithdraw_dispatch_compile (by rw [hlen]) (by decide) rootRightRightAPair_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xce96cb77, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xce, 0x96, 0xcb, 0x77, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk9.drop 59).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xce, 0x96, 0xcb, 0x77, 0x11] : Bytes) ++
      ([0x61, (2363 >>> 8).toUInt8, Nat.toUInt8 2363, 0x57] : Bytes) = (prorataWethVaultCodeChunk4.drop 67).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xce, 0x96, 0xcb, 0x77, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk4.drop 67).take 11) ++ (prorataWethVaultCodeChunk4.drop 78) = prorataWethVaultCodeChunk4.drop 67 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk4.drop 67)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk4.drop 67).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk9.take 59) ++ ((prorataWethVaultCodeChunk9.drop 59).take 1) = prorataWethVaultCodeChunk9.take 60 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk9) (i := 59) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 59), hj1]
  have hj2 : (prorataWethVaultCodeChunk9.take 60) ++ (prorataWethVaultCodeChunk9.drop 60) = prorataWethVaultCodeChunk9 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 60 (prorataWethVaultCodeChunk9)
  rw [← List.append_assoc (prorataWethVaultCodeChunk9.take 60), hj2]

private theorem rootRightRight_dispatch_compile :
    Func.compile vaultTable 28 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 23 rootRightRight)) = some (prorataWethVaultCodeChunk0.drop 28 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111) := by
  rw [rootRightRight_dispatch_node]
  have hcut : dispatchNode (selector "maxRedeem" [.address]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightRightA)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightRightB)) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "maxRedeem" [.address]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightRightB)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 22 rootRightRightA)) := by rfl
  rw [hcut, compile_prepend, maxRedeemSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xd905777e, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk0.drop 39 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4.take 66).length = 1051 := by decide +kernel
  have hbranch := compile_branch vaultTable 35 1090 _ _
    (prorataWethVaultCodeChunk0.drop 39 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4.take 66) (prorataWethVaultCodeChunk4.drop 67 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111)
    rootRightRightB_dispatch_compile (by rw [hlen]) (by decide) rootRightRightA_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xd905777e, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xd9, 0x5, 0x77, 0x7e, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk4.drop 66).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xd9, 0x5, 0x77, 0x7e, 0x11] : Bytes) ++
      ([0x61, (1090 >>> 8).toUInt8, Nat.toUInt8 1090, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 28).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xd9, 0x5, 0x77, 0x7e, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 28).take 11) ++ (prorataWethVaultCodeChunk0.drop 39) = prorataWethVaultCodeChunk0.drop 28 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk0.drop 28)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 28).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk4.take 66) ++ ((prorataWethVaultCodeChunk4.drop 66).take 1) = prorataWethVaultCodeChunk4.take 67 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk4) (i := 66) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk4.take 66), hj1]
  have hj2 : (prorataWethVaultCodeChunk4.take 67) ++ (prorataWethVaultCodeChunk4.drop 67) = prorataWethVaultCodeChunk4 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 67 (prorataWethVaultCodeChunk4)
  rw [← List.append_assoc (prorataWethVaultCodeChunk4.take 67), hj2]

private theorem rootRight_dispatch_compile :
    Func.compile vaultTable 17 (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 24 rootRight)) = some (prorataWethVaultCodeChunk0.drop 17 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) := by
  rw [rootRight_dispatch_node]
  have hcut : dispatchNode (selector "maxMint" [.address]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 23 rootRightLeft)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 23 rootRightRight)) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "maxMint" [.address]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 23 rootRightRight)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 23 rootRightLeft)) := by rfl
  rw [hcut, compile_prepend, maxMintSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0xc63d75b6, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk0.drop 28 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111).length = 4179 := by decide +kernel
  have hbranch := compile_branch vaultTable 24 4207 _ _
    (prorataWethVaultCodeChunk0.drop 28 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16.take 111) (prorataWethVaultCodeChunk16.drop 112 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218)
    rootRightRight_dispatch_compile (by rw [hlen]) (by decide) rootRightLeft_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0xc63d75b6, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0xc6, 0x3d, 0x75, 0xb6, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk16.drop 111).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0xc6, 0x3d, 0x75, 0xb6, 0x11] : Bytes) ++
      ([0x61, (4207 >>> 8).toUInt8, Nat.toUInt8 4207, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 17).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0xc6, 0x3d, 0x75, 0xb6, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 17).take 11) ++ (prorataWethVaultCodeChunk0.drop 28) = prorataWethVaultCodeChunk0.drop 17 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk0.drop 17)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 17).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk16.take 111) ++ ((prorataWethVaultCodeChunk16.drop 111).take 1) = prorataWethVaultCodeChunk16.take 112 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk16) (i := 111) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 111), hj1]
  have hj2 : (prorataWethVaultCodeChunk16.take 112) ++ (prorataWethVaultCodeChunk16.drop 112) = prorataWethVaultCodeChunk16 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 112 (prorataWethVaultCodeChunk16)
  rw [← List.append_assoc (prorataWethVaultCodeChunk16.take 112), hj2]

private theorem vaultTree_dispatch_compile :
    Func.compile vaultTable 6 (dispatchWith ProrataWethVault.revertSlot (ProrataWethVault.vaultTree)) = some (prorataWethVaultCodeChunk0.drop 6 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35 ++ prorataWethVaultCodeChunk36 ++ prorataWethVaultCodeChunk37 ++ prorataWethVaultCodeChunk38 ++ prorataWethVaultCodeChunk39 ++ prorataWethVaultCodeChunk40 ++ prorataWethVaultCodeChunk41 ++ prorataWethVaultCodeChunk42 ++ prorataWethVaultCodeChunk43 ++ prorataWethVaultCodeChunk44 ++ prorataWethVaultCodeChunk45 ++ prorataWethVaultCodeChunk46 ++ prorataWethVaultCodeChunk47 ++ prorataWethVaultCodeChunk48 ++ prorataWethVaultCodeChunk49 ++ prorataWethVaultCodeChunk50 ++ prorataWethVaultCodeChunk51 ++ prorataWethVaultCodeChunk52 ++ prorataWethVaultCodeChunk53 ++ prorataWethVaultCodeChunk54 ++ prorataWethVaultCodeChunk55 ++ prorataWethVaultCodeChunk56 ++ prorataWethVaultCodeChunk57 ++ prorataWethVaultCodeChunk58 ++ prorataWethVaultCodeChunk59 ++ prorataWethVaultCodeChunk60 ++ prorataWethVaultCodeChunk61.take 47) := by
  rw [vaultTree_dispatch_node]
  have hcut : dispatchNode (selector "mint" [.uint256, .address]) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 24 rootLeft)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 24 rootRight)) =
      ([Ninst.dup 0, Ninst.pushB256 (selector "mint" [.uint256, .address]), Ninst.gt] : Line) +++ Func.branch (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 24 rootRight)) (dispatchWith ProrataWethVault.revertSlot (DispatchTree.build 24 rootLeft)) := by rfl
  rw [hcut, compile_prepend, mintSelector_value]
  all_goals discharge_prepend_acceptance
  have hsize : prefixByteSize [Ninst.dup 0, Ninst.pushB256 0x94bf804d, Ninst.gt] = 7 := by rfl
  rw [hsize]
  simp only [Nat.reduceAdd]
  have hlen : (prorataWethVaultCodeChunk0.drop 17 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218).length = 9161 := by
    simp only [List.length_append, List.length_drop, List.length_take]
    decide +kernel
  have hbranch := compile_branch vaultTable 13 9178 _ _
    (prorataWethVaultCodeChunk0.drop 17 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35.take 218) (prorataWethVaultCodeChunk35.drop 219 ++ prorataWethVaultCodeChunk36 ++ prorataWethVaultCodeChunk37 ++ prorataWethVaultCodeChunk38 ++ prorataWethVaultCodeChunk39 ++ prorataWethVaultCodeChunk40 ++ prorataWethVaultCodeChunk41 ++ prorataWethVaultCodeChunk42 ++ prorataWethVaultCodeChunk43 ++ prorataWethVaultCodeChunk44 ++ prorataWethVaultCodeChunk45 ++ prorataWethVaultCodeChunk46 ++ prorataWethVaultCodeChunk47 ++ prorataWethVaultCodeChunk48 ++ prorataWethVaultCodeChunk49 ++ prorataWethVaultCodeChunk50 ++ prorataWethVaultCodeChunk51 ++ prorataWethVaultCodeChunk52 ++ prorataWethVaultCodeChunk53 ++ prorataWethVaultCodeChunk54 ++ prorataWethVaultCodeChunk55 ++ prorataWethVaultCodeChunk56 ++ prorataWethVaultCodeChunk57 ++ prorataWethVaultCodeChunk58 ++ prorataWethVaultCodeChunk59 ++ prorataWethVaultCodeChunk60 ++ prorataWethVaultCodeChunk61.take 47)
    rootRight_dispatch_compile (by rw [hlen]) (by decide) rootLeft_dispatch_compile
  rw [hbranch]
  have hbytes : ([Ninst.dup 0, Ninst.pushB256 0x94bf804d, Ninst.gt] : Line).flatMap Ninst.toBytes = [0x80, 0x63, 0x94, 0xbf, 0x80, 0x4d, 0x11] := by rfl
  rw [hbytes]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hjump : ([0x5b] : Bytes) = (prorataWethVaultCodeChunk35.drop 218).take 1 := by rfl
  have hprefix : ([0x80, 0x63, 0x94, 0xbf, 0x80, 0x4d, 0x11] : Bytes) ++
      ([0x61, (9178 >>> 8).toUInt8, Nat.toUInt8 9178, 0x57] : Bytes) = (prorataWethVaultCodeChunk0.drop 6).take 11 := by rfl
  rw [hjump, ← List.append_assoc ([0x80, 0x63, 0x94, 0xbf, 0x80, 0x4d, 0x11] : Bytes), hprefix]
  try simp only [List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 6).take 11) ++ (prorataWethVaultCodeChunk0.drop 17) = prorataWethVaultCodeChunk0.drop 6 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 11 (prorataWethVaultCodeChunk0.drop 6)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 6).take 11), hj0]
  have hj1 : (prorataWethVaultCodeChunk35.take 218) ++ ((prorataWethVaultCodeChunk35.drop 218).take 1) = prorataWethVaultCodeChunk35.take 219 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      (List.take_add (l := prorataWethVaultCodeChunk35) (i := 218) (j := 1)).symm
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 218), hj1]
  have hj2 : (prorataWethVaultCodeChunk35.take 219) ++ (prorataWethVaultCodeChunk35.drop 219) = prorataWethVaultCodeChunk35 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 219 (prorataWethVaultCodeChunk35)
  rw [← List.append_assoc (prorataWethVaultCodeChunk35.take 219), hj2]

private theorem vaultMain_source_cut : ProrataWethVault.vault.main =
    fsig +++ dispatchWith ProrataWethVault.revertSlot ProrataWethVault.vaultTree := by rfl

theorem vaultMain_compile :
    Func.compile vaultTable 1 (ProrataWethVault.vault.main) = some (prorataWethVaultCodeChunk0.drop 1 ++ prorataWethVaultCodeChunk1 ++ prorataWethVaultCodeChunk2 ++ prorataWethVaultCodeChunk3 ++ prorataWethVaultCodeChunk4 ++ prorataWethVaultCodeChunk5 ++ prorataWethVaultCodeChunk6 ++ prorataWethVaultCodeChunk7 ++ prorataWethVaultCodeChunk8 ++ prorataWethVaultCodeChunk9 ++ prorataWethVaultCodeChunk10 ++ prorataWethVaultCodeChunk11 ++ prorataWethVaultCodeChunk12 ++ prorataWethVaultCodeChunk13 ++ prorataWethVaultCodeChunk14 ++ prorataWethVaultCodeChunk15 ++ prorataWethVaultCodeChunk16 ++ prorataWethVaultCodeChunk17 ++ prorataWethVaultCodeChunk18 ++ prorataWethVaultCodeChunk19 ++ prorataWethVaultCodeChunk20 ++ prorataWethVaultCodeChunk21 ++ prorataWethVaultCodeChunk22 ++ prorataWethVaultCodeChunk23 ++ prorataWethVaultCodeChunk24 ++ prorataWethVaultCodeChunk25 ++ prorataWethVaultCodeChunk26 ++ prorataWethVaultCodeChunk27 ++ prorataWethVaultCodeChunk28 ++ prorataWethVaultCodeChunk29 ++ prorataWethVaultCodeChunk30 ++ prorataWethVaultCodeChunk31 ++ prorataWethVaultCodeChunk32 ++ prorataWethVaultCodeChunk33 ++ prorataWethVaultCodeChunk34 ++ prorataWethVaultCodeChunk35 ++ prorataWethVaultCodeChunk36 ++ prorataWethVaultCodeChunk37 ++ prorataWethVaultCodeChunk38 ++ prorataWethVaultCodeChunk39 ++ prorataWethVaultCodeChunk40 ++ prorataWethVaultCodeChunk41 ++ prorataWethVaultCodeChunk42 ++ prorataWethVaultCodeChunk43 ++ prorataWethVaultCodeChunk44 ++ prorataWethVaultCodeChunk45 ++ prorataWethVaultCodeChunk46 ++ prorataWethVaultCodeChunk47 ++ prorataWethVaultCodeChunk48 ++ prorataWethVaultCodeChunk49 ++ prorataWethVaultCodeChunk50 ++ prorataWethVaultCodeChunk51 ++ prorataWethVaultCodeChunk52 ++ prorataWethVaultCodeChunk53 ++ prorataWethVaultCodeChunk54 ++ prorataWethVaultCodeChunk55 ++ prorataWethVaultCodeChunk56 ++ prorataWethVaultCodeChunk57 ++ prorataWethVaultCodeChunk58 ++ prorataWethVaultCodeChunk59 ++ prorataWethVaultCodeChunk60 ++ prorataWethVaultCodeChunk61.take 47) := by
  have hb0 : fsig.flatMap Ninst.toBytes = (prorataWethVaultCodeChunk0.drop 1).take 5 := by
    rfl
  rw [vaultMain_source_cut]
  rw [compile_prepend, prefixByteSize_fsig]
  all_goals discharge_prepend_acceptance
  simp only [Nat.reduceAdd]
  rw [vaultTree_dispatch_compile, hb0]
  simp only [bind, Option.bind, pure, Pure.pure, List.append_assoc]
  have hj0 : ((prorataWethVaultCodeChunk0.drop 1).take 5) ++ (prorataWethVaultCodeChunk0.drop 6) = prorataWethVaultCodeChunk0.drop 1 := by
    simpa only [List.drop_drop, Nat.reduceAdd] using
      List.take_append_drop 5 (prorataWethVaultCodeChunk0.drop 1)
  rw [← List.append_assoc ((prorataWethVaultCodeChunk0.drop 1).take 5), hj0]

theorem vault_transferEvent_value : transferEvent = (0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef : B256) := by decide +kernel

theorem vault_depositEvent_value : ProrataWethVault.depositEvent = (0xdcbc1c05240f31ff3ad067ef1ee35ce4997762752e3a095284754544f4c709d7 : B256) := by decide +kernel

theorem vault_withdrawEvent_value : ProrataWethVault.withdrawEvent = (0xfbde797d201c681b91056529119e0b02407c7bb96a4a2c75c01fc9667232c8db : B256) := by decide +kernel

theorem vault_wethTransferFromSelector_value : ProrataWethVault.wethTransferFromSelector = (0x23b872dd : B256) := by decide +kernel

theorem vault_wethTransferSelector_value : ProrataWethVault.wethTransferSelector = (0xa9059cbb : B256) := by decide +kernel


end ProrataWethVaultCodeProof
end Blanc
