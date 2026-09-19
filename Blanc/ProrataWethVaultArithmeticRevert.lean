-- ProrataWethVaultArithmeticRevert.lean : the vault's full-width arithmetic,
-- read along a walk that settles at an arbitrary outcome.

import Blanc.ProrataWethVaultCapacities
import Blanc.RevertCause

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Revert-aware arithmetic adapters

The family's arithmetic traces are `Func.WalkInv`-generic, and every one of
them eliminates a revert arm through `WalkInv.noRevert`: they describe a walk
that succeeded.  A revert-cause theorem walks a frame that reverted, so its
revert arms are refuted by the theorem's own premises instead.

Only one arithmetic revert site is reachable from the capacity views:
`divide512`'s zero-denominator guard.  The capped quotient modes have no
overflow revert, and a nonzero denominator sends the walk into a body with no
`REVERT` terminal at all.  The staging before that guard is pure line code, so
it is read from the family's own line traces through `Func.Run.prepend_stop`;
nothing here restates them.
-/

section

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func}
  {sevm : Sevm}

/-- Past the zero-denominator guard, a capped `divide512` has no `REVERT`. -/
theorem divide512_capped_tail_revertFreeIn {safe : List Nat} {k : Nat}
    {mode : QuotientMode}
    (capped : mode = .capDown ∨ mode = .capCeilPred)
    (safeK : k ∈ safe) :
    Func.revertFreeIn safe
      (loadWord highWord +++ iszero :::
        (divideSimple mode k <?> divideWide mode k)) = true := by
  rcases capped with rfl | rfl <;>
    simp [Func.revertFreeIn_prepend, Func.revertFreeIn, divideSimple,
      divideWide, divideWideCore, finishQuotient, divisionOverflow, safeK]

/-- A capped `divide512` whose staged denominator is nonzero has no reverting
walk, once its continuation table is revert-free. -/
theorem divide512_capped_no_revert {pre d : Devm} {image : Bytes}
    {denominator : B256} {mode : QuotientMode} {k : Nat} {safe : List Nat}
    {tail : Stack}
    (capped : mode = .capDown ∨ mode = .capCeilPred)
    (safeK : k ∈ safe)
    (tableSafe : ∀ j ∈ safe, ∀ g, fs[j]? = some g →
      Func.revertFreeIn safe g = true)
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (denominatorNonzero : denominator ≠ 0)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (divide512 mode k) (.error (.revert, d))) : False := by
  unfold divide512 at run
  obtain ⟨loadPost, loadRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨loadPrefix, -, -, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt loadRun
  obtain ⟨testPre, zeroRun, -, branchRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have testPrefix :=
    prefix_of_iszero (Ninst.Run.of_runCompiled zeroRun) loadPrefix
  have zeroPrefix : (0 : B256) :: tail <<+ testPre.stack := by
    simpa [B256.eqCheck, denominatorNonzero] using testPrefix
  obtain ⟨restPre, -, restRun, -⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  exact Func.RunCompiledTo.not_revert_of_revertFreeIn tableSafe restRun.1
    (divide512_capped_tail_revertFreeIn capped safeK) d rfl

/-- A capped `mulDiv` whose produced denominator is nonzero has no reverting
walk.  The staging is read through the family's `ProducesWord.store_trace`
and `multiply512_trace`, exactly as `mulDiv_staging_trace` composes them. -/
theorem mulDiv_capped_no_revert {pre d : Devm} {image : Bytes}
    {x y denominator : B256} {xLine yLine denominatorLine : Line}
    {mode : QuotientMode} {k : Nat} {safe : List Nat} {tail : Stack}
    (capped : mode = .capDown ∨ mode = .capCeilPred)
    (safeK : k ∈ safe)
    (tableSafe : ∀ j ∈ safe, ∀ g, fs[j]? = some g →
      Func.revertFreeIn safe g = true)
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorProduces :
      ProducesWord sevm denominatorLine image denominator)
    (xProduces : ProducesWord sevm xLine
      (Bytes.writeAt image (denominatorWord * 32).toNat
        denominator.toBytes) x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt
        (Bytes.writeAt image (denominatorWord * 32).toNat
          denominator.toBytes)
        (xWord * 32).toNat x.toBytes) y)
    (denominatorNonzero : denominator ≠ 0)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (mulDiv xLine yLine denominatorLine mode k) (.error (.revert, d))) :
    False := by
  let staging : Line :=
    denominatorLine ++ mstoreAt denominatorWord ++
      (xLine ++ mstoreAt xWord ++ yLine ++ mstoreAt yWord ++
        multiply512ArithmeticLine)
  have split : ∀ body : Func,
      denominatorLine +++ mstoreAt denominatorWord +++
          multiply512 xLine yLine body = staging +++ body := by
    intro body
    simp only [staging, multiply512_eq_producers_arithmetic, prepend_append]
  have walkSplit : mulDiv xLine yLine denominatorLine mode k =
      staging +++ divide512 mode k := split _
  rw [walkSplit] at run
  obtain ⟨dividePre, stagingRun, divideRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  have sourceRun : Func.Run fs sevm pre
      (denominatorLine +++ mstoreAt denominatorWord +++
        multiply512 xLine yLine Func.stop) dividePre := by
    rw [split]
    exact Func.Run.prepend_stop stagingRun
  obtain ⟨multiplyPre, multiplyPrefix, multiplyWf, multiplyReads, -,
      multiplyRun⟩ :=
    denominatorProduces.store_trace (R := Func.Run) memoryWf memoryReads
      stack sourceRun
  obtain ⟨bodyPre, bodyPrefix, bodyWf, bodyReads, -, bodyRun⟩ :=
    multiply512_trace (R := Func.Run) multiplyWf multiplyReads xProduces
      yProduces multiplyPrefix multiplyRun
  obtain rfl := Func.Run.stop_inv bodyRun
  exact divide512_capped_no_revert capped safeK tableSafe bodyWf bodyReads
    (mulDivTraceImage_denominator image x y denominator) denominatorNonzero
    bodyPrefix divideRun

/-- A capped `shiftedDiv` whose produced denominator is nonzero has no
reverting walk. -/
theorem shiftedDiv_capped_no_revert {pre d : Devm} {image : Bytes}
    {high denominator : B256} {highLine denominatorLine : Line}
    {mode : QuotientMode} {k : Nat} {safe : List Nat} {tail : Stack}
    (capped : mode = .capDown ∨ mode = .capCeilPred)
    (safeK : k ∈ safe)
    (tableSafe : ∀ j ∈ safe, ∀ g, fs[j]? = some g →
      Func.revertFreeIn safe g = true)
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (highProduces : ProducesWord sevm highLine image high)
    (denominatorProduces : ProducesWord sevm denominatorLine
      (Bytes.writeAt
        (Bytes.writeAt image (highWord * 32).toNat high.toBytes)
        (lowWord * 32).toNat (0 : B256).toBytes) denominator)
    (denominatorNonzero : denominator ≠ 0)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (shiftedDiv highLine denominatorLine mode k) (.error (.revert, d))) :
    False := by
  let staging : Line :=
    highLine ++ mstoreAt highWord ++ ([pushB256 0] ++ mstoreAt lowWord ++
      (denominatorLine ++ mstoreAt denominatorWord))
  have split : ∀ body : Func,
      highLine +++ mstoreAt highWord +++ [pushB256 0] +++ mstoreAt lowWord +++
          denominatorLine +++ mstoreAt denominatorWord +++ body =
        staging +++ body := by
    intro body
    simp only [staging, prepend_append]
  have walkSplit : shiftedDiv highLine denominatorLine mode k =
      staging +++ divide512 mode k := split _
  rw [walkSplit] at run
  obtain ⟨dividePre, stagingRun, divideRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  have sourceRun : Func.Run fs sevm pre
      (highLine +++ mstoreAt highWord +++ [pushB256 0] +++ mstoreAt lowWord +++
        denominatorLine +++ mstoreAt denominatorWord +++ Func.stop)
      dividePre := by
    rw [split]
    exact Func.Run.prepend_stop stagingRun
  obtain ⟨lowPre, lowPrefix, lowWf, lowReads, -, lowRun⟩ :=
    highProduces.store_trace (R := Func.Run) memoryWf memoryReads stack
      sourceRun
  obtain ⟨denominatorPre, denominatorPrefix, denominatorWf,
      denominatorReads, -, denominatorRun⟩ :=
    ProducesWord.store_trace (R := Func.Run)
      (ProducesWord.pushB256 sevm
        (Bytes.writeAt image (highWord * 32).toNat high.toBytes) 0)
      lowWf lowReads lowPrefix lowRun
  obtain ⟨bodyPre, bodyPrefix, bodyWf, bodyReads, -, bodyRun⟩ :=
    denominatorProduces.store_trace (R := Func.Run) denominatorWf
      denominatorReads denominatorPrefix denominatorRun
  obtain rfl := Func.Run.stop_inv bodyRun
  exact divide512_capped_no_revert capped safeK tableSafe bodyWf bodyReads
    (shiftedDivTraceImage_denominator image high denominator)
    denominatorNonzero bodyPrefix divideRun

/-- Select the exact-max or ordinary arm after a proved word producer and the
shared `isMax` line, along an avoiding walk.  The step for step counterpart
of `ProducesWord.isMax_arm_trace`, whose revert-free guard it follows. -/
theorem ProducesWord.isMax_arm_avoiding {pre : Devm} {out : Execution}
    {line : Line} {image : Bytes} {value : B256}
    {maxBody ordinaryBody : Func} {tail : Stack}
    (produces : ProducesWord sevm line image value)
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (line +++ isMax +++ (maxBody <?> ordinaryBody)) out) :
    (value = B256.max ∧
      ∃ bodyPre, tail <<+ bodyPre.stack ∧ Mem.Wf bodyPre.memory ∧
        Mem.Reads bodyPre.memory image ∧
        Func.RunCompiledToAvoiding P fs sevm bodyPre maxBody out) ∨
    (value ≠ B256.max ∧
      ∃ bodyPre, tail <<+ bodyPre.stack ∧ Mem.Wf bodyPre.memory ∧
        Mem.Reads bodyPre.memory image ∧
        Func.RunCompiledToAvoiding P fs sevm bodyPre ordinaryBody out) := by
  obtain ⟨valuePre, valueRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨valuePrefix, valueWf, valueReads, -⟩ :=
    produces memoryWf memoryReads stack valueRun
  obtain ⟨testPre, testRun, branchRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  simp only [isMax] at testRun
  rcases Line.of_run_cons testRun with ⟨notPre, notRun, testRun⟩
  rcases Line.of_run_cons testRun with ⟨testPre', zeroRun, testRun⟩
  cases testRun
  have testPrefix :=
    prefix_of_iszero zeroRun (prefix_of_not notRun valuePrefix)
  have testMemory : valuePre.memory = testPre.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons notRun (Line.Run.cons zeroRun Line.Run.nil))
  by_cases valueMax : value = B256.max
  · have onePrefix : (1 : B256) :: tail <<+ testPre.stack := by
      simpa [valueMax, B256.not_max, B256.eqCheck] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have bodyMemory : valuePre.memory = bodyPre.memory :=
      testMemory.trans bodyPop.memory
    exact Or.inl ⟨valueMax, bodyPre, bodyPrefix, bodyMemory ▸ valueWf,
      bodyMemory ▸ valueReads, bodyRun⟩
  · have notNonzero : (~~~ value) ≠ 0 := by
      intro notZero
      exact valueMax (B256.eq_max_of_not_eq_zero notZero)
    have zeroPrefix : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.eqCheck, notNonzero] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
    have bodyMemory : valuePre.memory = bodyPre.memory :=
      testMemory.trans bodyPop.memory
    exact Or.inr ⟨valueMax, bodyPre, bodyPrefix, bodyMemory ▸ valueWf,
      bodyMemory ▸ valueReads, bodyRun⟩

/-- The staged share denominator is a nonzero word at a stable supply. -/
theorem stagedDenominator_ne_zero {supply : B256}
    (stable : supply.toNat ≤ maxSupplyN) :
    Nat.toB256 (denominatorN supply.toNat) ≠ 0 := by
  intro zero
  have nat := congrArg B256.toNat zero
  rw [stagedDenominator_toNat stable] at nat
  exact Nat.ne_of_gt (denominatorN_pos supply.toNat) nat

/-- Away from the all-ones asset word, the staged asset factor is a nonzero
word. -/
theorem stagedAssetFactor_ne_zero {assets : B256} (notMax : assets ≠ B256.max) :
    Nat.toB256 (assetFactorN assets.toNat) ≠ 0 := by
  intro zero
  have nat := congrArg B256.toNat zero
  rw [stagedAssetFactor_toNat_of_ne_max notMax] at nat
  exact Nat.ne_of_gt (assetFactorN_pos assets.toNat) nat

/-- `returnWord` is the only continuation the `maxDeposit`/`maxWithdraw`
arithmetic calls, and it has no `REVERT`. -/
theorem returnWord_table_revertFree
    (returnLookup : fs[returnWordSlot]? = some returnWord) :
    ∀ j ∈ [returnWordSlot], ∀ g, fs[j]? = some g →
      Func.revertFreeIn [returnWordSlot] g = true := by
  intro j member g lookup
  rw [List.mem_singleton] at member
  subst member
  rw [returnLookup] at lookup
  cases lookup
  decide

/-- `maxMint`'s asset-cap continuation and `returnWord` have no `REVERT`. -/
theorem maxMintCap_table_revertFree
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (capLookup : fs[maxMintAfterAssetCapSlot]? = some maxMintAfterAssetCap) :
    ∀ j ∈ [maxMintAfterAssetCapSlot, returnWordSlot], ∀ g, fs[j]? = some g →
      Func.revertFreeIn [maxMintAfterAssetCapSlot, returnWordSlot] g =
        true := by
  intro j member g lookup
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [capLookup] at lookup
    cases lookup
    decide
  · rw [returnLookup] at lookup
    cases lookup
    decide

/-- After the WETH balance word reaches the stack, the `maxDeposit` body has
no reverting walk at a stable supply. -/
theorem maxDeposit_postTotalAssets_no_revert {pre d : Devm} {image : Bytes}
    {assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : assets :: tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv shareRoomPlusOne stagedDenominator .capCeilPred
            returnWordSlot <?>
          mulDiv shareRoomPlusOne stagedAssetFactor stagedDenominator
            .capCeilPred returnWordSlot)) (.error (.revert, d))) : False := by
  obtain ⟨arithmeticPre, storeRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨arithmeticStack, arithmeticWf, arithmeticReads, -⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads storeRun
  have arithmeticSupplyWindow :
      MemWordAt arithmeticPre (supplyWord * 32).toNat supply :=
    supplyWindow.acrossMstoreAt (Or.inl (by decide +kernel)) storeRun
  change Mem.Reads arithmeticPre.memory (capacityAssetsImage image assets)
    at arithmeticReads
  have supplyAt : Bytes.toB256
      ((capacityAssetsImage image assets).sliceD
        (supplyWord * 32).toNat 32 0) = supply := by
    rw [arithmeticSupplyWindow.slice_eq arithmeticReads, B256.toB256_toBytes]
  have assetsAt := capacityAssetsImage_assets image assets
  rcases ProducesWord.isMax_arm_avoiding (ProducesWord.loadWord assetsAt)
      arithmeticWf arithmeticReads arithmeticStack run with
    ⟨-, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩ |
      ⟨-, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
  · exact shiftedDiv_capped_no_revert (Or.inr rfl)
      (List.mem_singleton_self _) (returnWord_table_revertFree returnLookup)
      bodyWf bodyReads (ProducesWord.shareRoomPlusOne supplyAt stable)
      (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
      (stagedDenominator_ne_zero stable) bodyStack bodyRun
  · exact mulDiv_capped_no_revert (Or.inr rfl)
      (List.mem_singleton_self _) (returnWord_table_revertFree returnLookup)
      bodyWf bodyReads (ProducesWord.stagedDenominator supplyAt)
      (ProducesWord.shareRoomPlusOne_after_denominatorScratch supplyAt stable)
      (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
      (stagedDenominator_ne_zero stable) bodyStack bodyRun

/-- After the WETH balance word reaches the stack, the `maxMint` body has no
reverting walk.  Its exact-max arm divides by `2^256` and has no revert
site; its ordinary arm divides by the nonzero asset factor, so no supply bound
is needed. -/
theorem maxMint_postTotalAssets_no_revert {pre d : Devm} {image : Bytes}
    {assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stack : assets :: tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (capLookup :
      fs[maxMintAfterAssetCapSlot]? = some maxMintAfterAssetCap)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
            maxMintAfterAssetCapSlot <?>
          mulDiv [pushB256 B256.max] stagedDenominator stagedAssetFactor
            .capDown maxMintAfterAssetCapSlot)) (.error (.revert, d))) :
    False := by
  obtain ⟨arithmeticPre, storeRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨arithmeticStack, arithmeticWf, arithmeticReads, -⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads storeRun
  have arithmeticSupplyWindow :
      MemWordAt arithmeticPre (supplyWord * 32).toNat supply :=
    supplyWindow.acrossMstoreAt (Or.inl (by decide +kernel)) storeRun
  change Mem.Reads arithmeticPre.memory (capacityAssetsImage image assets)
    at arithmeticReads
  have supplyAt : Bytes.toB256
      ((capacityAssetsImage image assets).sliceD
        (supplyWord * 32).toNat 32 0) = supply := by
    rw [arithmeticSupplyWindow.slice_eq arithmeticReads, B256.toB256_toBytes]
  have assetsAt := capacityAssetsImage_assets image assets
  have tableSafe := maxMintCap_table_revertFree returnLookup capLookup
  rcases ProducesWord.isMax_arm_avoiding (ProducesWord.loadWord assetsAt)
      arithmeticWf arithmeticReads arithmeticStack run with
    ⟨-, bodyPre, -, -, -, bodyRun⟩ |
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
  · have free : Func.revertFreeIn [maxMintAfterAssetCapSlot, returnWordSlot]
        (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
          maxMintAfterAssetCapSlot) = true := by
      simp [productOverTwoPow256, multiply512, finishQuotient,
        Func.revertFreeIn_prepend, Func.revertFreeIn]
    exact Func.RunCompiledTo.not_revert_of_revertFreeIn tableSafe bodyRun.1
      free d rfl
  · exact mulDiv_capped_no_revert (Or.inl rfl)
      (List.mem_cons_self ..) tableSafe bodyWf bodyReads
      (ProducesWord.stagedAssetFactor assetsAt)
      (ProducesWord.pushB256 sevm
        (Bytes.writeAt (capacityAssetsImage image assets)
          (denominatorWord * 32).toNat
          (Nat.toB256 (assetFactorN assets.toNat)).toBytes) B256.max)
      (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
      (stagedAssetFactor_ne_zero assetsNotMax) bodyStack bodyRun

/-- After the WETH balance word reaches the stack, the `maxWithdraw` body has
no reverting walk at a stable supply. -/
theorem maxWithdraw_postTotalAssets_no_revert {pre d : Devm} {image : Bytes}
    {amount assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (amountWindow : MemWordAt pre (amountWord * 32).toNat amount)
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : assets :: tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .capDown
            returnWordSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .capDown returnWordSlot)) (.error (.revert, d))) : False := by
  obtain ⟨arithmeticPre, storeRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨arithmeticStack, arithmeticWf, arithmeticReads, -⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads storeRun
  have arithmeticAmountWindow :
      MemWordAt arithmeticPre (amountWord * 32).toNat amount :=
    amountWindow.acrossMstoreAt (Or.inl (by decide +kernel)) storeRun
  have arithmeticSupplyWindow :
      MemWordAt arithmeticPre (supplyWord * 32).toNat supply :=
    supplyWindow.acrossMstoreAt (Or.inl (by decide +kernel)) storeRun
  change Mem.Reads arithmeticPre.memory (capacityAssetsImage image assets)
    at arithmeticReads
  have amountAt : Bytes.toB256
      ((capacityAssetsImage image assets).sliceD
        (amountWord * 32).toNat 32 0) = amount := by
    rw [arithmeticAmountWindow.slice_eq arithmeticReads, B256.toB256_toBytes]
  have supplyAt : Bytes.toB256
      ((capacityAssetsImage image assets).sliceD
        (supplyWord * 32).toNat 32 0) = supply := by
    rw [arithmeticSupplyWindow.slice_eq arithmeticReads, B256.toB256_toBytes]
  have assetsAt := capacityAssetsImage_assets image assets
  rcases ProducesWord.isMax_arm_avoiding (ProducesWord.loadWord assetsAt)
      arithmeticWf arithmeticReads arithmeticStack run with
    ⟨-, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩ |
      ⟨-, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
  · exact shiftedDiv_capped_no_revert (Or.inl rfl)
      (List.mem_singleton_self _) (returnWord_table_revertFree returnLookup)
      bodyWf bodyReads (ProducesWord.loadWord amountAt)
      (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
      (stagedDenominator_ne_zero stable) bodyStack bodyRun
  · exact mulDiv_capped_no_revert (Or.inl rfl)
      (List.mem_singleton_self _) (returnWord_table_revertFree returnLookup)
      bodyWf bodyReads (ProducesWord.stagedDenominator supplyAt)
      (ProducesWord.amount_after_denominatorScratch amountAt)
      (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
      (stagedDenominator_ne_zero stable) bodyStack bodyRun

/-! ### Capacity-view routes along an avoiding walk -/

/-- `returnConstant` has no `REVERT` and calls nothing. -/
theorem returnConstant_revertFreeIn (w : B256) :
    Func.revertFreeIn [] (returnConstant w) = true := by
  simp [returnConstant, returnWord, returnMemoryRange, Func.return_,
    Func.revertFreeIn_prepend, Func.revertFreeIn]

/-- A reverting walk that meets a `returnConstant` arm has taken the other. -/
theorem returnConstant_no_revert {pre d : Devm} {w : B256}
    (run : Func.RunCompiledTo fs sevm pre (returnConstant w)
      (.error (.revert, d))) : False :=
  Func.RunCompiledTo.not_revert_of_revertFreeIn (safe := [])
    (fun _ member => absurd member List.not_mem_nil) run
    (returnConstant_revertFreeIn w) d rfl

/-- The zero-address route of `maxMint`/`maxDeposit` returns zero, so a
reverting walk passes it with a nonzero argument. -/
theorem zeroArgCapacityBranch_revert {pre d : Devm} {body : Func}
    {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (arg 0 +++ iszero ::: (returnConstant 0 <?> body))
      (.error (.revert, d))) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧ Mem.Wf bodyPre.memory ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body
        (.error (.revert, d)) := by
  obtain ⟨testPre, argRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have argPrefix : Sevm.argWord sevm 0 :: tail <<+ testPre.stack :=
    prefix_of_arg stack argRun
  have argState : pre.state = testPre.state :=
    Line.of_inv Devm.state (by unfold Blanc.arg cdl; line_inv) argRun
  have argMemory : pre.memory = testPre.memory :=
    Line.of_inv Devm.memory (by unfold Blanc.arg cdl; line_inv) argRun
  obtain ⟨branchPre, zeroRun, -, branchRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have zeroSource := Ninst.Run.of_runCompiled zeroRun
  have testPrefix := prefix_of_iszero zeroSource argPrefix
  by_cases argZero : Sevm.argWord sevm 0 = 0
  · have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.eqCheck, argZero] using testPrefix
    obtain ⟨zeroPre, -, zeroRoute, -⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    exact (returnConstant_no_revert zeroRoute.1).elim
  · have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.eqCheck, argZero] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
    have bodyPop' := Devm.PopBurn.of_popBurnBy bodyPop
    refine ⟨bodyPre, bodyPrefix, ?_, ?_, bodyRun⟩
    · rw [← bodyPop'.memory, ← Ninst.Hinv.inv (f := Devm.memory) zeroSource,
        ← argMemory]
      exact memoryWf
    · exact argState.trans
        ((Ninst.Hinv.inv (f := Devm.state) zeroSource).trans bodyPop'.state)

/-- Stage the share supply along an avoiding walk.  Read from the family's
`capacitySupplyStaging_trace` through the `STOP` bridge. -/
theorem capacitySupplyStaging_avoiding {pre : Devm} {out : Execution}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++ body) out) :
    ∃ supply bodyPre,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      tail <<+ bodyPre.stack ∧
      MemWordAt bodyPre (supplyWord * 32).toNat supply ∧
      (∀ {offset : Nat} {w : B256},
        (offset + 32 ≤ (supplyWord * 32).toNat ∨
          (supplyWord * 32).toNat + 32 ≤ offset) →
        MemWordAt pre offset w → MemWordAt bodyPre offset w) ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  have split : ∀ tailFunc : Func,
      pushSupplySlot +++ sload ::: mstoreAt supplyWord +++ tailFunc =
        (pushSupplySlot ++ [sload] ++ mstoreAt supplyWord) +++ tailFunc := by
    intro tailFunc
    simp only [prepend_append]
    rfl
  rw [split] at run
  obtain ⟨bodyPre, line, bodyRun⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have source : Func.Run fs sevm pre
      (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++ Func.stop)
      bodyPre := by
    rw [split]
    exact Func.Run.prepend_stop line
  obtain ⟨supply, tracePre, supplyEq, tracePrefix, window, preserves, state,
      -, stopRun⟩ :=
    capacitySupplyStaging_trace (R := Func.Run) memoryWf stack source
  obtain rfl := Func.Run.stop_inv stopRun
  exact ⟨supply, bodyPre, supplyEq, tracePrefix, window, preserves, state,
    bodyRun⟩

/-- Stage the owner's share balance along an avoiding walk. -/
theorem capacityAmountStaging_avoiding {pre : Devm} {out : Execution}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (arg 0 +++ sload ::: mstoreAt amountWord +++ body) out) :
    ∃ amount bodyPre,
      amount = Devm.getStorVal pre sevm.currentTarget (Sevm.argWord sevm 0) ∧
      tail <<+ bodyPre.stack ∧
      MemWordAt bodyPre (amountWord * 32).toNat amount ∧
      pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  have split : ∀ tailFunc : Func,
      arg 0 +++ sload ::: mstoreAt amountWord +++ tailFunc =
        (arg 0 ++ [sload] ++ mstoreAt amountWord) +++ tailFunc := by
    intro tailFunc
    simp only [prepend_append]
    rfl
  rw [split] at run
  obtain ⟨bodyPre, line, bodyRun⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have source : Func.Run fs sevm pre
      (arg 0 +++ sload ::: mstoreAt amountWord +++ Func.stop) bodyPre := by
    rw [split]
    exact Func.Run.prepend_stop line
  obtain ⟨amount, tracePre, amountEq, tracePrefix, window, state, -,
      stopRun⟩ :=
    capacityAmountStaging_trace (R := Func.Run) memoryWf stack source
  obtain rfl := Func.Run.stop_inv stopRun
  exact ⟨amount, bodyPre, amountEq, tracePrefix, window, state, bodyRun⟩

/-- The stable-supply domain check of the capacity views returns zero on an
unstable supply, so a reverting walk passes it with a stable one. -/
theorem stableCapacityBranch_revert {pre d : Devm} {supply : B256}
    {body : Func} {tail : Stack}
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
        (returnConstant 0 <?> body)) (.error (.revert, d))) :
    supply.toNat ≤ maxSupplyN ∧
      ∃ bodyPre,
        tail <<+ bodyPre.stack ∧
        (∀ {offset : Nat} {w : B256}, MemWordAt pre offset w →
          MemWordAt bodyPre offset w) ∧
        pre.state = bodyPre.state ∧
        Func.RunCompiledToAvoiding P fs sevm bodyPre body
          (.error (.revert, d)) := by
  obtain ⟨maxPre, supplyRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have supplyPrefix := prefix_of_loadWord_window supplyWindow stack supplyRun
  have supplyState : pre.state = maxPre.state :=
    Line.of_inv Devm.state (by unfold loadWord; line_inv) supplyRun
  obtain ⟨testPre, maxRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have maxSource := Ninst.Run.of_runCompiled maxRun
  have maxPrefix := prefix_of_push (of_run_pushB256 maxSource) supplyPrefix
  obtain ⟨branchPre, testRun, -, branchRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource maxPrefix
  by_cases unstable : maxSupply < supply
  · have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.ltCheck, unstable] using testPrefix
    obtain ⟨zeroPre, -, zeroRoute, -⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    exact (returnConstant_no_revert zeroRoute.1).elim
  · have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.ltCheck, unstable] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
    have bodyPop' := Devm.PopBurn.of_popBurnBy bodyPop
    have stableWord : supply ≤ maxSupply := B256.not_lt.mp unstable
    have stable : supply.toNat ≤ maxSupplyN := by
      rw [B256.le_iff_toNat_le_toNat, maxSupply_toNat] at stableWord
      exact stableWord
    refine ⟨stable, bodyPre, bodyPrefix, ?_, ?_, bodyRun⟩
    · intro offset w window
      exact MemWordAt.of_memory_eq bodyPop'.memory.symm
        (((window.acrossLoadWord supplyRun).acrossNinst maxSource).acrossNinst
          testSource)
    · exact supplyState.trans
        ((Ninst.Hinv.inv (f := Devm.state) maxSource).trans
          ((Ninst.Hinv.inv (f := Devm.state) testSource).trans bodyPop'.state))

end

end ProrataWethVault

end Blanc
