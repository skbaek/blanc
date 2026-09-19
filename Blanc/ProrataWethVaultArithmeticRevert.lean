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


/-! ## Uncapped quotients along an avoiding walk

The flows divide in the `.down` and `.up` modes, whose revert sites are the
zero-denominator guard, the wide-overflow guard and the ceiling-overflow
guard.  Each is refuted by the flow's own bound on the exact quotient.  The
walk is replayed as a source run in `Func.stopTable k`, so the family's
success traces read the quotient off that run, and the walk continues,
still avoiding, in the real continuation body. -/

section

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List Func}
  {sevm : Sevm}

/-- A fixed-word load pushes one word above any known stack prefix. -/
theorem loadWord_head {pre post : Devm} {w : B256} {tail : Stack}
    (stack : tail <<+ pre.stack)
    (run : Line.Run sevm pre (loadWord w) post) :
    ∃ v, v :: tail <<+ post.stack := by
  rcases Line.of_run_cons run with ⟨afterPush, pushRun, run⟩
  rcases Line.of_run_cons run with ⟨_, loadRun, hnil⟩
  cases hnil
  have pushed := of_run_pushB256 pushRun
  have selfReads : Mem.Reads afterPush.memory
      afterPush.memory.data.toList := by
    intro index
    simp
  obtain ⟨loaded, -, -⟩ :=
    prefix_of_mload_val loadRun (prefix_of_push pushed stack) selfReads
  exact ⟨_, loaded⟩

/-- Ceiling finishing along an avoiding walk: either the walk passes the
rounding guard into the continuation, or it loaded a nonzero remainder and
the all-ones quotient, which the `capCeilPred` finisher replays exactly. -/
theorem finishQuotient_up_split {pre : Devm} {out : Execution} {k : Nat}
    {body : Func}
    (lookup : fs[k]? = some body)
    (run : Func.RunCompiledToAvoiding P fs sevm pre (finishQuotient .up k)
      out) :
    (∃ mid, Func.Run (Func.stopTable k) sevm pre (finishQuotient .up k) mid ∧
        Func.RunCompiledToAvoiding P fs sevm mid body out) ∨
      (∃ remainderPost remainder final,
        Line.Run sevm pre (loadWord remainderWord) remainderPost ∧
        remainder :: [] <<+ remainderPost.stack ∧ remainder ≠ 0 ∧
        Func.Run (Func.stopTable k) sevm pre (finishQuotient .capCeilPred k)
          final ∧
        B256.max :: [] <<+ final.stack) := by
  simp only [finishQuotient] at run ⊢
  obtain ⟨remPost, remRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨remw, remStack⟩ := loadWord_head nil_pref remRun
  obtain ⟨testPost, zeroRun, -, branchRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have zeroSource := Ninst.Run.of_runCompiled zeroRun
  have testPrefix := prefix_of_iszero zeroSource remStack
  by_cases remZero : remw = 0
  · have onePrefix : (1 : B256) :: [] <<+ testPost.stack := by
      simpa [B256.eqCheck, remZero] using testPrefix
    obtain ⟨armPre, pop, armRun, -⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix (by decide) onePrefix
        branchRun
    obtain ⟨mid, armSource, bodyRun⟩ :=
      Func.RunCompiledToAvoiding.lineCall_inv
        (f := loadWord quotientWord +++ .call k) rfl lookup armRun
    exact Or.inl ⟨mid, Func.Run.prepend_line remRun (Func.Run.next zeroSource
      (Func.Run.succ_of_popBurnBy (by decide) pop armSource)), bodyRun⟩
  · have zeroPrefix : (0 : B256) :: [] <<+ testPost.stack := by
      simpa [B256.eqCheck, remZero] using testPrefix
    obtain ⟨armPre, pop, armRun, -⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
    obtain ⟨qPost, qRun, armRun⟩ := Func.RunCompiledToAvoiding.prepend_inv armRun
    obtain ⟨qw, qStack⟩ := loadWord_head nil_pref qRun
    obtain ⟨dupPost, dupRun, -, armRun⟩ :=
      Func.RunCompiledToAvoiding.next_inv armRun
    have dupSource := Ninst.Run.of_runCompiled dupRun
    have dupPrefix : qw :: qw :: [] <<+ dupPost.stack :=
      prefix_of_dup_val dupSource (by show_nth) qStack
    obtain ⟨maxPost, maxRun, branch2⟩ :=
      Func.RunCompiledToAvoiding.prepend_inv armRun
    simp only [isMax] at maxRun
    rcases Line.of_run_cons maxRun with ⟨notPost, notRun, maxRun⟩
    rcases Line.of_run_cons maxRun with ⟨_, zero2Run, hnil⟩
    cases hnil
    have maxPrefix :=
      prefix_of_iszero zero2Run (prefix_of_not notRun dupPrefix)
    by_cases qMax : qw = B256.max
    · have lastRun : Func.Run (Func.stopTable k) sevm armPre
          (loadWord quotientWord +++ .call k) qPost :=
        Func.Run.prepend_line qRun (Func.Run.call (Func.stopTable_get k)
          Devm.Burn.refl (Func.Run.last rfl))
      refine Or.inr ⟨remPost, remw, qPost, remRun, remStack, remZero,
        Func.Run.prepend_line remRun (Func.Run.next zeroSource
          (Func.Run.zero_of_popBurnBy pop lastRun)), ?_⟩
      rw [← qMax]
      exact qStack
    · have notNonzero : (~~~ qw) ≠ 0 := by
        intro notZero
        exact qMax (B256.eq_max_of_not_eq_zero notZero)
      have zeroPrefix2 : (0 : B256) :: qw :: [] <<+ maxPost.stack := by
        simpa [B256.eqCheck, notNonzero] using maxPrefix
      obtain ⟨roundPre, pop2, roundRun, -⟩ :=
        Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix2 branch2
      obtain ⟨mid, roundSource, bodyRun⟩ :=
        Func.RunCompiledToAvoiding.lineCall_inv
          (f := pushB256 1 ::: add ::: .call k) rfl lookup roundRun
      refine Or.inl ⟨mid, Func.Run.prepend_line remRun (Func.Run.next zeroSource
        (Func.Run.zero_of_popBurnBy pop (Func.Run.prepend_line qRun
          (Func.Run.next dupSource (Func.Run.prepend_line
            (Line.Run.cons notRun (Line.Run.cons zero2Run Line.Run.nil))
            (Func.Run.zero_of_popBurnBy pop2 roundSource)))))), bodyRun⟩


/-- With the entry image known, a ceiling finisher whose quotient cannot
round past the word passes into its continuation. -/
theorem finishQuotient_up_run {pre : Devm} {out : Execution} {image : Bytes}
    {quotient remainder : B256} {k : Nat} {body : Func}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (quotientAt : Bytes.toB256
      (image.sliceD (quotientWord * 32).toNat 32 0) = quotient)
    (remainderAt : Bytes.toB256
      (image.sliceD (remainderWord * 32).toNat 32 0) = remainder)
    (safe : remainder ≠ 0 → quotient ≠ B256.max)
    (lookup : fs[k]? = some body)
    (run : Func.RunCompiledToAvoiding P fs sevm pre (finishQuotient .up k)
      out) :
    ∃ mid, Func.Run (Func.stopTable k) sevm pre (finishQuotient .up k) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid body out := by
  rcases finishQuotient_up_split lookup run with done |
      ⟨remPost, remw, final, remRun, remStack, remNonzero, capRun, maxStack⟩
  · exact done
  · exfalso
    obtain ⟨remPrefix, -, -, -⟩ :=
      of_run_loadWordAt_image nil_pref memoryWf memoryReads remainderAt remRun
    have remEq : remainder = remw := pref_head_unique remPrefix remStack
    subst remEq
    obtain ⟨bodyPre, valuePrefix, stopRun⟩ :=
      finishQuotient_capCeilPred_trace (R := Func.Run) memoryWf memoryReads
        quotientAt remainderAt nil_pref (Func.stopTable_get k) capRun
    obtain rfl := Func.Run.stop_inv stopRun
    have valueMax := pref_head_unique valuePrefix maxStack
    rw [if_neg remNonzero] at valueMax
    exact safe remNonzero valueMax

/-- The straight-line half of `divideSimple`. -/
def simpleDivisionLine : Line :=
  loadWord denominatorWord ++ loadWord lowWord ++ [mod] ++
    mstoreAt remainderWord ++
    (loadWord denominatorWord ++ loadWord lowWord ++ [div] ++
      mstoreAt quotientWord)

theorem divideSimple_eq_line (mode : QuotientMode) (k : Nat) :
    divideSimple mode k = simpleDivisionLine +++ finishQuotient mode k := by
  simp [divideSimple, simpleDivisionLine, prepend_append, List.append_assoc,
    prepend]

theorem ProducesWord.loadsMod {image : Bytes} {denominator low : B256}
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low) :
    ProducesWord sevm (ProrataWethVault.loadWord denominatorWord ++
      ProrataWethVault.loadWord lowWord ++ [mod])
      image (low % denominator) := by
  intro pre post tail memoryWf memoryReads stack run
  rcases of_run_append _ run with ⟨s2, loads, opLine⟩
  rcases of_run_append _ loads with ⟨s1, dRun, lowRun⟩
  obtain ⟨p1, wf1, reads1, st1⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt dRun
  obtain ⟨p2, wf2, reads2, st2⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 lowAt lowRun
  rcases Line.of_run_cons opLine with ⟨s3, opRun, hnil⟩
  cases hnil
  have memory3 : s2.memory = post.memory :=
    Ninst.Hinv.inv (f := Devm.memory) opRun
  refine ⟨prefix_of_mod opRun p2, ?_, ?_,
    (Devm.QuietFrame.mk' st1 (of_run_loadWordAt_logs dRun)).trans
      ((Devm.QuietFrame.mk' st2 (of_run_loadWordAt_logs lowRun)).trans
        (Devm.QuietFrame.ofNinst opRun))⟩
  · rw [← memory3]
    exact wf2
  · rw [← memory3]
    exact reads2

theorem ProducesWord.loadsDiv {image : Bytes} {denominator low : B256}
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low) :
    ProducesWord sevm (ProrataWethVault.loadWord denominatorWord ++
      ProrataWethVault.loadWord lowWord ++ [div])
      image (low / denominator) := by
  intro pre post tail memoryWf memoryReads stack run
  rcases of_run_append _ run with ⟨s2, loads, opLine⟩
  rcases of_run_append _ loads with ⟨s1, dRun, lowRun⟩
  obtain ⟨p1, wf1, reads1, st1⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt dRun
  obtain ⟨p2, wf2, reads2, st2⟩ :=
    of_run_loadWordAt_image p1 wf1 reads1 lowAt lowRun
  rcases Line.of_run_cons opLine with ⟨s3, opRun, hnil⟩
  cases hnil
  have memory3 : s2.memory = post.memory :=
    Ninst.Hinv.inv (f := Devm.memory) opRun
  refine ⟨prefix_of_div opRun p2, ?_, ?_,
    (Devm.QuietFrame.mk' st1 (of_run_loadWordAt_logs dRun)).trans
      ((Devm.QuietFrame.mk' st2 (of_run_loadWordAt_logs lowRun)).trans
        (Devm.QuietFrame.ofNinst opRun))⟩
  · rw [← memory3]
    exact wf2
  · rw [← memory3]
    exact reads2

/-- The straight-line half of `divideSimple`, read at any line run. -/
theorem simpleDivisionLine_image {pre mid : Devm} {image : Bytes}
    {denominator low : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (stack : tail <<+ pre.stack)
    (line : Line.Run sevm pre simpleDivisionLine mid) :
    tail <<+ mid.stack ∧ Mem.Wf mid.memory ∧
      Mem.Reads mid.memory (simpleDivisionTraceImage image low denominator) ∧
      Devm.QuietFrame pre mid := by
  have split : simpleDivisionLine +++ Func.stop =
      (loadWord denominatorWord ++ loadWord lowWord ++ [mod]) +++
        mstoreAt remainderWord +++
        (loadWord denominatorWord ++ loadWord lowWord ++ [div]) +++
        mstoreAt quotientWord +++ Func.stop := by
    simp only [simpleDivisionLine, prepend_append]
  have source : Func.Run ([] : List Func) sevm pre
      ((loadWord denominatorWord ++ loadWord lowWord ++ [mod]) +++
        mstoreAt remainderWord +++
        (loadWord denominatorWord ++ loadWord lowWord ++ [div]) +++
        mstoreAt quotientWord +++ Func.stop) mid := by
    rw [← split]
    exact Func.Run.prepend_stop line
  obtain ⟨s4, p4, wf4, reads4, st4, run⟩ :=
    ProducesWord.store_trace (R := Func.Run)
      (ProducesWord.loadsMod (sevm := sevm) denominatorAt lowAt) memoryWf memoryReads stack source
  let image1 := Bytes.writeAt image
    (remainderWord * 32).toNat (low % denominator).toBytes
  change Mem.Reads s4.memory image1 at reads4
  have denominatorAt1 : Bytes.toB256
      (image1.sliceD (denominatorWord * 32).toNat 32 0) = denominator := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact denominatorAt
    · left
      decide +kernel
  have lowAt1 : Bytes.toB256
      (image1.sliceD (lowWord * 32).toNat 32 0) = low := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact lowAt
    · left
      decide +kernel
  obtain ⟨s8, p8, wf8, reads8, st8, run⟩ :=
    ProducesWord.store_trace (R := Func.Run)
      (ProducesWord.loadsDiv (sevm := sevm) denominatorAt1 lowAt1) wf4 reads4 p4 run
  obtain rfl := Func.Run.stop_inv run
  exact ⟨p8, wf8, by simpa [simpleDivisionTraceImage, image1] using reads8,
    st4.trans st8⟩

/-- A word quotient of a nonzero remainder division is never the all-ones
word. -/
theorem simpleQuotient_ne_max {low denominator : B256}
    (denominatorNonzero : denominator ≠ 0)
    (remainderNonzero : low % denominator ≠ 0) :
    low / denominator ≠ B256.max := by
  intro quotientMax
  have natQ := congrArg B256.toNat quotientMax
  rw [B256.toNat_div denominatorNonzero, maxWord_toNat] at natQ
  have natR : low.toNat % denominator.toNat ≠ 0 := by
    intro zero
    apply remainderNonzero
    apply B256.toNat_inj
    rw [B256.toNat_mod denominatorNonzero, zero]
    rfl
  have dNe : denominator.toNat ≠ 1 := by
    intro one
    rw [one, Nat.mod_one] at natR
    exact natR rfl
  have dPos : denominator.toNat ≠ 0 := B256.toNat_ne_zero denominatorNonzero
  have lowLt := B256.toNat_lt low
  have le : low.toNat / denominator.toNat ≤ low.toNat / 2 :=
    Nat.div_le_div_left (by omega) (by omega)
  unfold maxWordN wordModulusN at natQ
  omega

/-- A wide numerator's floor quotient fits a word only below the
denominator's high word. -/
theorem high_lt_of_wide_fits {high low denominator : B256}
    (denominatorNonzero : denominator ≠ 0)
    (fits : wideNumeratorN high low / denominator.toNat < wordModulusN) :
    high < denominator := by
  by_contra notLt
  have le : denominator.toNat ≤ high.toNat := by
    by_contra h
    exact notLt (B256.lt_of_toNat_lt_toNat (by omega))
  have dPos : 0 < denominator.toNat :=
    Nat.pos_of_ne_zero (B256.toNat_ne_zero denominatorNonzero)
  have big : wordModulusN ≤ wideNumeratorN high low / denominator.toNat := by
    rw [Nat.le_div_iff_mul_le dPos]
    unfold wideNumeratorN
    calc wordModulusN * denominator.toNat
        ≤ wordModulusN * high.toNat := Nat.mul_le_mul_left _ le
      _ = high.toNat * wordModulusN := Nat.mul_comm _ _
      _ ≤ high.toNat * wordModulusN + low.toNat := Nat.le_add_right _ _
  omega

theorem floor_lt_of_ceilDiv_lt {n d : Nat} (fits : ceilDiv n d < wordModulusN) :
    n / d < wordModulusN := by
  unfold ceilDiv at fits
  split at fits <;> omega

/-- Floor division along an avoiding walk, replayed as a `STOP`-table source
run up to the continuation. -/
theorem divide512_down_run {pre : Devm} {out : Execution} {image : Bytes}
    {denominator high low : B256} {k : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (denominatorNonzero : denominator ≠ 0)
    (fits : wideNumeratorN high low / denominator.toNat < wordModulusN)
    (stack : tail <<+ pre.stack)
    (lookup : fs[k]? = some body)
    (run : Func.RunCompiledToAvoiding P fs sevm pre (divide512 .down k) out) :
    ∃ mid, Func.Run (Func.stopTable k) sevm pre (divide512 .down k) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid body out := by
  unfold divide512 at run ⊢
  obtain ⟨s1, dRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt dRun
  obtain ⟨s2, zRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have zSource := Ninst.Run.of_runCompiled zRun
  have p2 : (0 : B256) :: tail <<+ s2.stack := by
    simpa [B256.eqCheck, denominatorNonzero] using prefix_of_iszero zSource p1
  obtain ⟨s3, pop, run, p3⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix p2 run
  have memory3 : s1.memory = s3.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) zSource).trans
      (Devm.PopBurn.of_popBurnBy pop).memory
  have wf3 : Mem.Wf s3.memory := memory3 ▸ wf1
  have reads3 : Mem.Reads s3.memory image := memory3 ▸ reads1
  obtain ⟨s4, hRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_loadWordAt_image p3 wf3 reads3 highAt hRun
  obtain ⟨s5, z2Run, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have z2Source := Ninst.Run.of_runCompiled z2Run
  have flag := prefix_of_iszero z2Source p4
  by_cases highZero : high = 0
  · have onePrefix : (1 : B256) :: tail <<+ s5.stack := by
      simpa [B256.eqCheck, highZero] using flag
    obtain ⟨s6, pop2, run, -⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix (by decide) onePrefix
        run
    obtain ⟨mid, simpleSource, bodyRun⟩ :=
      Func.RunCompiledToAvoiding.lineCall_inv
        (f := divideSimple .down k) rfl lookup run
    exact ⟨mid, Func.Run.prepend_line dRun (Func.Run.next zSource
      (Func.Run.zero_of_popBurnBy pop (Func.Run.prepend_line hRun
        (Func.Run.next z2Source
          (Func.Run.succ_of_popBurnBy (by decide) pop2 simpleSource))))),
      bodyRun⟩
  · have zeroPrefix : (0 : B256) :: tail <<+ s5.stack := by
      simpa [B256.eqCheck, highZero] using flag
    obtain ⟨s6, pop2, run, p6⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix run
    have memory6 : s4.memory = s6.memory :=
      (Ninst.Hinv.inv (f := Devm.memory) z2Source).trans
        (Devm.PopBurn.of_popBurnBy pop2).memory
    have wf6 : Mem.Wf s6.memory := memory6 ▸ wf4
    have reads6 : Mem.Reads s6.memory image := memory6 ▸ reads4
    unfold divideWide at run ⊢
    obtain ⟨s7, dRun2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨p7, wf7, reads7, -⟩ :=
      of_run_loadWordAt_image p6 wf6 reads6 denominatorAt dRun2
    obtain ⟨s8, hRun2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨p8, -, -, -⟩ :=
      of_run_loadWordAt_image p7 wf7 reads7 highAt hRun2
    obtain ⟨s9, ltRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
    have ltSource := Ninst.Run.of_runCompiled ltRun
    have noOverflow := high_lt_of_wide_fits denominatorNonzero fits
    have onePrefix : (1 : B256) :: tail <<+ s9.stack := by
      simpa [B256.ltCheck, noOverflow] using prefix_of_lt ltSource p8
    obtain ⟨s10, pop3, run, -⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix (by decide) onePrefix
        run
    have coreShape : (divideWideCore .down k).lineCall =
        some (wideCoreArithmeticLine ++ loadWord quotientWord, k) := by
      rw [divideWideCore_eq_arithmeticLine, Func.lineCall_prepend]
      rfl
    obtain ⟨mid, coreSource, bodyRun⟩ :=
      Func.RunCompiledToAvoiding.lineCall_inv coreShape lookup run
    exact ⟨mid, Func.Run.prepend_line dRun (Func.Run.next zSource
      (Func.Run.zero_of_popBurnBy pop (Func.Run.prepend_line hRun
        (Func.Run.next z2Source (Func.Run.zero_of_popBurnBy pop2
          (Func.Run.prepend_line dRun2 (Func.Run.prepend_line hRun2
            (Func.Run.next ltSource (Func.Run.succ_of_popBurnBy (by decide)
              pop3 coreSource))))))))), bodyRun⟩


/-- A word minus one is the all-ones word only at zero. -/
theorem eq_zero_of_sub_one_eq_max {q : B256} (h : q - 1 = B256.max) : q = 0 := by
  by_contra qNe
  have qPos := B256.toNat_ne_zero qNe
  have oneLe : (1 : B256) ≤ q := by
    rw [B256.le_iff_toNat_le_toNat]
    change 1 ≤ q.toNat
    omega
  have nat := congrArg B256.toNat h
  rw [B256.toNat_sub_eq_of_le _ _ oneLe, maxWord_toNat] at nat
  have qLt := B256.toNat_lt q
  change q.toNat - 1 = maxWordN at nat
  unfold maxWordN wordModulusN at nat
  omega

/-- Ceiling division along an avoiding walk, replayed as a `STOP`-table
source run up to the continuation.  The single-word arm reads its staged
quotient directly; the wide arm refutes the rounding guard through the
`capCeilPred` replay of the same staging. -/
theorem divide512_up_run {pre : Devm} {out : Execution} {image : Bytes}
    {denominator high low : B256} {k : Nat} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (denominatorAt : Bytes.toB256
      (image.sliceD (denominatorWord * 32).toNat 32 0) = denominator)
    (highAt : Bytes.toB256
      (image.sliceD (highWord * 32).toNat 32 0) = high)
    (lowAt : Bytes.toB256
      (image.sliceD (lowWord * 32).toNat 32 0) = low)
    (denominatorNonzero : denominator ≠ 0)
    (fits : ceilDiv (wideNumeratorN high low) denominator.toNat < wordModulusN)
    (stack : tail <<+ pre.stack)
    (lookup : fs[k]? = some body)
    (run : Func.RunCompiledToAvoiding P fs sevm pre (divide512 .up k) out) :
    ∃ mid, Func.Run (Func.stopTable k) sevm pre (divide512 .up k) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid body out := by
  have floorFits := floor_lt_of_ceilDiv_lt fits
  unfold divide512 at run ⊢
  obtain ⟨s1, dRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p1, wf1, reads1, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads denominatorAt dRun
  obtain ⟨s2, zRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have zSource := Ninst.Run.of_runCompiled zRun
  have p2 : (0 : B256) :: tail <<+ s2.stack := by
    simpa [B256.eqCheck, denominatorNonzero] using prefix_of_iszero zSource p1
  obtain ⟨s3, pop, run, p3⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix p2 run
  have memory3 : s1.memory = s3.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) zSource).trans
      (Devm.PopBurn.of_popBurnBy pop).memory
  have wf3 : Mem.Wf s3.memory := memory3 ▸ wf1
  have reads3 : Mem.Reads s3.memory image := memory3 ▸ reads1
  obtain ⟨s4, hRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p4, wf4, reads4, -⟩ :=
    of_run_loadWordAt_image p3 wf3 reads3 highAt hRun
  obtain ⟨s5, z2Run, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have z2Source := Ninst.Run.of_runCompiled z2Run
  have flag := prefix_of_iszero z2Source p4
  by_cases highZero : high = 0
  · have onePrefix : (1 : B256) :: tail <<+ s5.stack := by
      simpa [B256.eqCheck, highZero] using flag
    obtain ⟨s6, pop2, run, p6⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix (by decide) onePrefix
        run
    have memory6 : s4.memory = s6.memory :=
      (Ninst.Hinv.inv (f := Devm.memory) z2Source).trans
        (Devm.PopBurn.of_popBurnBy pop2).memory
    have wf6 : Mem.Wf s6.memory := memory6 ▸ wf4
    have reads6 : Mem.Reads s6.memory image := memory6 ▸ reads4
    rw [divideSimple_eq_line] at run
    obtain ⟨finishPre, simpleLine, run⟩ :=
      Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨-, finishWf, finishReads, -⟩ :=
      simpleDivisionLine_image wf6 reads6 denominatorAt lowAt p6 simpleLine
    obtain ⟨mid, finishSource, bodyRun⟩ :=
      finishQuotient_up_run finishWf finishReads
        (simpleDivisionTraceImage_quotient image low denominator)
        (simpleDivisionTraceImage_remainder image low denominator)
        (simpleQuotient_ne_max denominatorNonzero) lookup run
    have simpleSource : Func.Run (Func.stopTable k) sevm s6
        (divideSimple .up k) mid := by
      rw [divideSimple_eq_line]
      exact Func.Run.prepend_line simpleLine finishSource
    exact ⟨mid, Func.Run.prepend_line dRun (Func.Run.next zSource
      (Func.Run.zero_of_popBurnBy pop (Func.Run.prepend_line hRun
        (Func.Run.next z2Source
          (Func.Run.succ_of_popBurnBy (by decide) pop2 simpleSource))))),
      bodyRun⟩
  · have zeroPrefix : (0 : B256) :: tail <<+ s5.stack := by
      simpa [B256.eqCheck, highZero] using flag
    obtain ⟨s6, pop2, run, p6⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix run
    have memory6 : s4.memory = s6.memory :=
      (Ninst.Hinv.inv (f := Devm.memory) z2Source).trans
        (Devm.PopBurn.of_popBurnBy pop2).memory
    have wf6 : Mem.Wf s6.memory := memory6 ▸ wf4
    have reads6 : Mem.Reads s6.memory image := memory6 ▸ reads4
    unfold divideWide at run ⊢
    obtain ⟨s7, dRun2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨p7, wf7, reads7, -⟩ :=
      of_run_loadWordAt_image p6 wf6 reads6 denominatorAt dRun2
    obtain ⟨s8, hRun2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
    obtain ⟨p8, wf8, reads8, -⟩ :=
      of_run_loadWordAt_image p7 wf7 reads7 highAt hRun2
    obtain ⟨s9, ltRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
    have ltSource := Ninst.Run.of_runCompiled ltRun
    have noOverflow := high_lt_of_wide_fits denominatorNonzero floorFits
    have onePrefix : (1 : B256) :: tail <<+ s9.stack := by
      simpa [B256.ltCheck, noOverflow] using prefix_of_lt ltSource p8
    obtain ⟨s10, pop3, run, p10⟩ :=
      Func.RunCompiledToAvoiding.succ_branch_of_prefix (by decide) onePrefix
        run
    have memory10 : s8.memory = s10.memory :=
      (Ninst.Hinv.inv (f := Devm.memory) ltSource).trans
        (Devm.PopBurn.of_popBurnBy pop3).memory
    have wf10 : Mem.Wf s10.memory := memory10 ▸ wf8
    have reads10 : Mem.Reads s10.memory image := memory10 ▸ reads8
    rw [divideWideCore_eq_arithmeticLine] at run
    obtain ⟨finishPre, wideLine, run⟩ :=
      Func.RunCompiledToAvoiding.prepend_inv run
    rcases finishQuotient_up_split lookup run with
        ⟨mid, finishSource, bodyRun⟩ |
        ⟨-, -, final, -, -, -, capRun, maxStack⟩
    · have coreSource : Func.Run (Func.stopTable k) sevm s10
          (divideWideCore .up k) mid := by
        rw [divideWideCore_eq_arithmeticLine]
        exact Func.Run.prepend_line wideLine finishSource
      exact ⟨mid, Func.Run.prepend_line dRun (Func.Run.next zSource
        (Func.Run.zero_of_popBurnBy pop (Func.Run.prepend_line hRun
          (Func.Run.next z2Source (Func.Run.zero_of_popBurnBy pop2
            (Func.Run.prepend_line dRun2 (Func.Run.prepend_line hRun2
              (Func.Run.next ltSource (Func.Run.succ_of_popBurnBy (by decide)
                pop3 coreSource))))))))), bodyRun⟩
    · exfalso
      have capFull : Func.Run (Func.stopTable k) sevm s10
          (divideWideCore .capCeilPred k) final := by
        rw [divideWideCore_eq_arithmeticLine]
        exact Func.Run.prepend_line wideLine capRun
      obtain ⟨stagedPre, stagedImage, stagedStack, stagedWf, stagedReads,
          quotientAt, remainderAt, -, -, stagedRun⟩ :=
        divideWideCore_staging_trace (R := Func.Run) wf10 reads10
          denominatorAt highAt lowAt p10 capFull
      obtain ⟨bodyPre, valuePrefix, stopRun⟩ :=
        finishQuotient_capCeilPred_trace (R := Func.Run) stagedWf stagedReads
          quotientAt remainderAt stagedStack (Func.stopTable_get k) stagedRun
      obtain rfl := Func.Run.stop_inv stopRun
      have valueMax := pref_head_unique valuePrefix maxStack
      have denominatorZero' : denominator ≠ B256.zero := denominatorNonzero
      have quotientEq :=
        wideQuotientWord_eq_toB256 (low := low) denominatorZero' noOverflow
      have remainderIff :=
        wideRemainderWord_eq_zero_iff (high := high) (low := low)
          denominatorZero'
      by_cases remainderZero : wideRemainderWord high low denominator = 0
      · rw [if_pos remainderZero] at valueMax
        have quotientZero := eq_zero_of_sub_one_eq_max valueMax
        rw [quotientEq] at quotientZero
        have nat := congrArg B256.toNat quotientZero
        rw [B256.toNat_toB256_of_lt floorFits] at nat
        change wideNumeratorN high low / denominator.toNat = 0 at nat
        have dPos : 0 < denominator.toNat :=
          Nat.pos_of_ne_zero (B256.toNat_ne_zero denominatorNonzero)
        have below : wideNumeratorN high low < denominator.toNat := by
          by_contra notBelow
          have := Nat.div_pos (Nat.le_of_not_lt notBelow) dPos
          omega
        have highPos := B256.toNat_ne_zero highZero
        have dLt := B256.toNat_lt denominator
        have wideBig : wordModulusN ≤ wideNumeratorN high low := by
          unfold wideNumeratorN
          calc wordModulusN = 1 * wordModulusN := (Nat.one_mul _).symm
            _ ≤ high.toNat * wordModulusN :=
                Nat.mul_le_mul_right _ (by omega)
            _ ≤ high.toNat * wordModulusN + low.toNat := Nat.le_add_right _ _
        unfold wordModulusN at wideBig
        omega
      · rw [if_neg remainderZero] at valueMax
        rw [quotientEq] at valueMax
        have nat := congrArg B256.toNat valueMax
        rw [B256.toNat_toB256_of_lt floorFits, maxWord_toNat] at nat
        have natRem : wideNumeratorN high low % denominator.toNat ≠ 0 :=
          fun zero => remainderZero (remainderIff.mpr zero)
        unfold ceilDiv at fits
        rw [if_neg natRem, nat] at fits
        unfold maxWordN wordModulusN at fits
        omega


/-- Select the exact-max or ordinary arm after a proved word producer and the
shared `isMax` line, keeping the lift of any `STOP`-table source run of the
selected arm back to the whole selection. -/
theorem ProducesWord.isMax_split {pre : Devm} {out : Execution}
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
        Func.RunCompiledToAvoiding P fs sevm bodyPre maxBody out ∧
        ∀ (table : List Func) (mid : Devm),
          Func.Run table sevm bodyPre maxBody mid →
          Func.Run table sevm pre
            (line +++ isMax +++ (maxBody <?> ordinaryBody)) mid) ∨
    (value ≠ B256.max ∧
      ∃ bodyPre, tail <<+ bodyPre.stack ∧ Mem.Wf bodyPre.memory ∧
        Mem.Reads bodyPre.memory image ∧
        Func.RunCompiledToAvoiding P fs sevm bodyPre ordinaryBody out ∧
        ∀ (table : List Func) (mid : Devm),
          Func.Run table sevm bodyPre ordinaryBody mid →
          Func.Run table sevm pre
            (line +++ isMax +++ (maxBody <?> ordinaryBody)) mid) := by
  obtain ⟨valuePre, valueRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨valuePrefix, valueWf, valueReads, -⟩ :=
    produces memoryWf memoryReads stack valueRun
  obtain ⟨testPre, testRun, branchRun⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  have testLine := testRun
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
      testMemory.trans (Devm.PopBurn.of_popBurnBy bodyPop).memory
    refine Or.inl ⟨valueMax, bodyPre, bodyPrefix, bodyMemory ▸ valueWf,
      bodyMemory ▸ valueReads, bodyRun, ?_⟩
    intro table mid source
    exact Func.Run.prepend_line valueRun (Func.Run.prepend_line testLine
      (Func.Run.succ_of_popBurnBy (by decide) bodyPop source))
  · have notNonzero : (~~~ value) ≠ 0 := by
      intro notZero
      exact valueMax (B256.eq_max_of_not_eq_zero notZero)
    have zeroPrefix : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.eqCheck, notNonzero] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
    have bodyMemory : valuePre.memory = bodyPre.memory :=
      testMemory.trans (Devm.PopBurn.of_popBurnBy bodyPop).memory
    refine Or.inr ⟨valueMax, bodyPre, bodyPrefix, bodyMemory ▸ valueWf,
      bodyMemory ▸ valueReads, bodyRun, ?_⟩
    intro table mid source
    exact Func.Run.prepend_line valueRun (Func.Run.prepend_line testLine
      (Func.Run.zero_of_popBurnBy bodyPop source))

/-- `mulDiv`'s staging along an avoiding walk, with the lift of a source run
of its `divide512` back to the whole `mulDiv`. -/
theorem mulDiv_split {pre : Devm} {out : Execution} {image : Bytes}
    {x y denominator : B256} {xLine yLine denominatorLine : Line}
    {mode : QuotientMode} {k : Nat} {tail : Stack}
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
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (mulDiv xLine yLine denominatorLine mode k) out) :
    ∃ dividePre, tail <<+ dividePre.stack ∧ Mem.Wf dividePre.memory ∧
      Mem.Reads dividePre.memory (mulDivTraceImage image x y denominator) ∧
      Func.RunCompiledToAvoiding P fs sevm dividePre (divide512 mode k) out ∧
      ∀ (table : List Func) (mid : Devm),
        Func.Run table sevm dividePre (divide512 mode k) mid →
        Func.Run table sevm pre (mulDiv xLine yLine denominatorLine mode k)
          mid := by
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
  refine ⟨dividePre, bodyPrefix, bodyWf, bodyReads, divideRun, ?_⟩
  intro table mid source
  rw [walkSplit]
  exact Func.Run.prepend_line stagingRun source

/-- `shiftedDiv`'s staging along an avoiding walk, with the lift of a source
run of its `divide512` back to the whole `shiftedDiv`. -/
theorem shiftedDiv_split {pre : Devm} {out : Execution} {image : Bytes}
    {high denominator : B256} {highLine denominatorLine : Line}
    {mode : QuotientMode} {k : Nat} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (highProduces : ProducesWord sevm highLine image high)
    (denominatorProduces : ProducesWord sevm denominatorLine
      (Bytes.writeAt
        (Bytes.writeAt image (highWord * 32).toNat high.toBytes)
        (lowWord * 32).toNat (0 : B256).toBytes) denominator)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (shiftedDiv highLine denominatorLine mode k) out) :
    ∃ dividePre, tail <<+ dividePre.stack ∧ Mem.Wf dividePre.memory ∧
      Mem.Reads dividePre.memory (shiftedDivTraceImage image high denominator) ∧
      Func.RunCompiledToAvoiding P fs sevm dividePre (divide512 mode k) out ∧
      ∀ (table : List Func) (mid : Devm),
        Func.Run table sevm dividePre (divide512 mode k) mid →
        Func.Run table sevm pre (shiftedDiv highLine denominatorLine mode k)
          mid := by
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
  refine ⟨dividePre, bodyPrefix, bodyWf, ?_, divideRun, ?_⟩
  · simpa [shiftedDivTraceImage] using bodyReads
  · intro table mid source
    rw [walkSplit]
    exact Func.Run.prepend_line stagingRun source

/-- The straight-line prefix of `productOverTwoPow256`. -/
def productLine (xLine yLine : Line) : Line :=
  xLine ++ mstoreAt xWord ++ yLine ++ mstoreAt yWord ++
    multiply512ArithmeticLine ++ loadWord highWord ++ mstoreAt quotientWord ++
    loadWord lowWord ++ mstoreAt remainderWord

theorem productOverTwoPow256_eq_line (xLine yLine : Line)
    (mode : QuotientMode) (k : Nat) :
    productOverTwoPow256 xLine yLine mode k =
      productLine xLine yLine +++ finishQuotient mode k := by
  simp only [productOverTwoPow256, productLine,
    multiply512_eq_producers_arithmetic, prepend_append]

theorem productOverTwoPow256_down_lineCall (xLine yLine : Line) (k : Nat) :
    (productOverTwoPow256 xLine yLine .down k).lineCall =
      some (productLine xLine yLine ++ loadWord quotientWord, k) := by
  rw [productOverTwoPow256_eq_line, Func.lineCall_prepend]
  rfl

/-- The straight-line prefix of `productOverTwoPow256`, read at any line
run. -/
theorem productLine_image {pre mid : Devm} {image : Bytes} {x y : B256}
    {xLine yLine : Line} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xProduces : ProducesWord sevm xLine image x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes) y)
    (stack : tail <<+ pre.stack)
    (line : Line.Run sevm pre (productLine xLine yLine) mid) :
    tail <<+ mid.stack ∧ Mem.Wf mid.memory ∧
      Mem.Reads mid.memory (productOverTwoPow256TraceImage image x y) := by
  have split : productLine xLine yLine +++ Func.stop =
      multiply512 xLine yLine
        (loadWord highWord +++ mstoreAt quotientWord +++
          loadWord lowWord +++ mstoreAt remainderWord +++ Func.stop) := by
    simp only [productLine, multiply512_eq_producers_arithmetic,
      prepend_append]
  have source : Func.Run ([] : List Func) sevm pre
      (multiply512 xLine yLine
        (loadWord highWord +++ mstoreAt quotientWord +++
          loadWord lowWord +++ mstoreAt remainderWord +++ Func.stop)) mid := by
    rw [← split]
    exact Func.Run.prepend_stop line
  obtain ⟨quotientPre, quotientPrefix, quotientWf, quotientReads, -, run⟩ :=
    multiply512_trace (R := Func.Run) memoryWf memoryReads xProduces
      yProduces stack source
  obtain ⟨remainderPre, remainderPrefix, remainderWf, remainderReads, -, run⟩ :=
    ProducesWord.store_trace (R := Func.Run)
      (ProducesWord.loadWord (multiply512TraceImage_high image x y))
      quotientWf quotientReads quotientPrefix run
  let image1 := Bytes.writeAt (multiply512TraceImage image x y)
    (quotientWord * 32).toNat (productHighWord x y).toBytes
  change Mem.Reads remainderPre.memory image1 at remainderReads
  have lowAt1 : Bytes.toB256
      (image1.sliceD (lowWord * 32).toNat 32 0) = productLowWord x y := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact multiply512TraceImage_low image x y
    · left
      decide +kernel
  obtain ⟨finishPre, finishPrefix, finishWf, finishReads, -, run⟩ :=
    ProducesWord.store_trace (R := Func.Run) (ProducesWord.loadWord lowAt1)
      remainderWf remainderReads remainderPrefix run
  obtain rfl := Func.Run.stop_inv run
  exact ⟨finishPrefix, finishWf,
    by simpa [productOverTwoPow256TraceImage, image1] using finishReads⟩

/-- A product's high word cannot round up past the word while the ceiling of
the product over `2^256` fits. -/
theorem productQuotient_ne_max {x y : B256}
    (fits : ceilDiv (x.toNat * y.toNat) wordModulusN < wordModulusN) :
    productLowWord x y ≠ 0 → productHighWord x y ≠ B256.max := by
  intro lowNe highMax
  rw [← wideNumeratorN_productWords] at fits
  have hNat := congrArg B256.toNat highMax
  rw [maxWord_toNat] at hNat
  have lPos := B256.toNat_ne_zero lowNe
  have lLt := B256.toNat_lt (productLowWord x y)
  have wPos : 0 < wordModulusN := by unfold wordModulusN; positivity
  unfold wideNumeratorN ceilDiv at fits
  have div : ((productHighWord x y).toNat * wordModulusN +
      (productLowWord x y).toNat) / wordModulusN =
      (productHighWord x y).toNat := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ wPos,
      Nat.div_eq_of_lt (by unfold wordModulusN; exact lLt)]
    simp
  have mod : ((productHighWord x y).toNat * wordModulusN +
      (productLowWord x y).toNat) % wordModulusN =
      (productLowWord x y).toNat := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by unfold wordModulusN; exact lLt)]
  rw [div, mod, if_neg lPos, hNat] at fits
  unfold maxWordN at fits
  omega

/-- Ceiling product-over-`2^256` along an avoiding walk. -/
theorem productOverTwoPow256_up_run {pre : Devm} {out : Execution}
    {image : Bytes} {x y : B256} {xLine yLine : Line} {k : Nat} {body : Func}
    {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (xProduces : ProducesWord sevm xLine image x)
    (yProduces : ProducesWord sevm yLine
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes) y)
    (fits : ceilDiv (x.toNat * y.toNat) wordModulusN < wordModulusN)
    (stack : tail <<+ pre.stack)
    (lookup : fs[k]? = some body)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (productOverTwoPow256 xLine yLine .up k) out) :
    ∃ mid, Func.Run (Func.stopTable k) sevm pre
        (productOverTwoPow256 xLine yLine .up k) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid body out := by
  rw [productOverTwoPow256_eq_line] at run ⊢
  obtain ⟨finishPre, line, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨-, finishWf, finishReads⟩ :=
    productLine_image memoryWf memoryReads xProduces yProduces stack line
  obtain ⟨mid, finishSource, bodyRun⟩ :=
    finishQuotient_up_run finishWf finishReads
      (productOverTwoPow256TraceImage_quotient image x y)
      (productOverTwoPow256TraceImage_remainder image x y)
      (productQuotient_ne_max fits) lookup run
  exact ⟨mid, Func.Run.prepend_line line finishSource, bodyRun⟩


/-! ### The four flow quotes along an avoiding walk -/

/-- `deposit`'s quote along an avoiding walk: the exact floor quote reaches
`depositAfterQuote` whenever it fits a word. -/
theorem depositQuote_avoiding {pre : Devm} {out : Execution}
    {image : Bytes} {amount assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (amountAt : Bytes.toB256
      (image.sliceD (amountWord * 32).toNat 32 0) = amount)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (lookup : fs[depositAfterQuoteSlot]? = some depositAfterQuote)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 (loadWord amountWord) stagedDenominator .down
            depositAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor
            .down depositAfterQuoteSlot)) out)
    (quoteFits :
      convertToSharesN amount.toNat assets.toNat supply.toNat < wordModulusN) :
    ∃ bodyPre bodyImage,
      Nat.toB256
          (convertToSharesN amount.toNat assets.toNat supply.toNat) ::
        tail <<+ bodyPre.stack ∧
      MemImage bodyPre bodyImage ∧
      Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
      Devm.QuietFrame pre bodyPre ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre depositAfterQuote out := by
  obtain ⟨mid, source, bodyRun⟩ : ∃ mid,
      Func.Run (Func.stopTable depositAfterQuoteSlot) sevm pre
        (loadWord assetsWord +++ isMax +++
          (productOverTwoPow256 (loadWord amountWord) stagedDenominator .down
              depositAfterQuoteSlot <?>
            mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor
              .down depositAfterQuoteSlot)) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid depositAfterQuote out := by
    rcases ProducesWord.isMax_split (ProducesWord.loadWord assetsAt) memoryWf
        memoryReads stack run with
      ⟨-, bodyPre, -, -, -, armRun, lift⟩ |
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, armRun, lift⟩
    · obtain ⟨mid, armSource, bodyRun⟩ :=
        Func.RunCompiledToAvoiding.lineCall_inv
          (productOverTwoPow256_down_lineCall _ _ _) lookup armRun
      exact ⟨mid, lift _ _ armSource, bodyRun⟩
    · obtain ⟨dividePre, divideStack, divideWf, divideReads, divideRun,
          divideLift⟩ :=
        mulDiv_split bodyWf bodyReads (ProducesWord.stagedAssetFactor assetsAt)
          (ProducesWord.amount_after_denominatorScratch amountAt)
          (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
          bodyStack armRun
      obtain ⟨mid, divideSource, bodyRun⟩ :=
        divide512_down_run divideWf divideReads
          (mulDivTraceImage_denominator _ _ _ _)
          (mulDivTraceImage_high _ _ _ _) (stagedAssetFactor_ne_zero assetsNotMax)
          (by
            rw [wideNumeratorN_productWords]
            simpa [convertToSharesN, stagedDenominator_toNat stable,
              stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteFits)
          divideStack lookup divideRun
      exact ⟨mid, lift _ _ (divideLift _ _ divideSource), bodyRun⟩
  have stopLookup := Func.stopTable_get depositAfterQuoteSlot
  rcases ProducesWord.isMax_arm_trace (R := Func.Run)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack source with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨-, quotePre, quoteStack, quoteImage, quoteState, quoteRun⟩ :=
      productOverTwoPow256_down_image_trace armWf armReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, productOverTwoPow256TraceImage image amount denominator, ?_,
      quoteImage,
      productOverTwoPow256TraceImage_wordFrame image amount denominator,
      armState.trans quoteState, bodyRun⟩
    simpa [convertToSharesN, denominator, assetsMax, maxWord_toNat,
      assetFactorN_maxWord, stagedDenominator_toNat stable] using quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    obtain ⟨-, quotePre, quoteImage, quoteStack, quoteMemImage, quoteFrame,
        quoteState, quoteRun⟩ :=
      mulDiv_down_image_trace armWf armReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, quoteImage, ?_, quoteMemImage, quoteFrame,
      armState.trans quoteState, bodyRun⟩
    simpa [convertToSharesN, stagedDenominator_toNat stable,
      stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack


/-- `mint`'s quote along an avoiding walk: the exact ceiling quote reaches
`mintAfterQuote` whenever it fits a word. -/
theorem mintQuote_avoiding {pre : Devm} {out : Execution}
    {image : Bytes} {amount assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (amountAt : Bytes.toB256
      (image.sliceD (amountWord * 32).toNat 32 0) = amount)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (lookup : fs[mintAfterQuoteSlot]? = some mintAfterQuote)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .up
            mintAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .up mintAfterQuoteSlot)) out)
    (quoteFits : previewMintN amount.toNat assets.toNat supply.toNat < wordModulusN) :
    ∃ bodyPre bodyImage,
      Nat.toB256 (previewMintN amount.toNat assets.toNat supply.toNat) ::
        tail <<+ bodyPre.stack ∧
      MemImage bodyPre bodyImage ∧
      Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
      Devm.QuietFrame pre bodyPre ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre mintAfterQuote out := by
  obtain ⟨mid, source, bodyRun⟩ : ∃ mid,
      Func.Run (Func.stopTable mintAfterQuoteSlot) sevm pre
        (loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .up
            mintAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .up mintAfterQuoteSlot)) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid mintAfterQuote out := by
    rcases ProducesWord.isMax_split (ProducesWord.loadWord assetsAt) memoryWf
        memoryReads stack run with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, armRun, lift⟩ |
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, armRun, lift⟩
    · obtain ⟨dividePre, divideStack, divideWf, divideReads, divideRun,
          divideLift⟩ :=
        shiftedDiv_split bodyWf bodyReads (ProducesWord.loadWord amountAt)
          (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
          bodyStack armRun
      obtain ⟨mid, divideSource, bodyRun⟩ :=
        divide512_up_run divideWf divideReads
          (shiftedDivTraceImage_denominator _ _ _)
          (shiftedDivTraceImage_high _ _ _) (shiftedDivTraceImage_low _ _ _)
          (stagedDenominator_ne_zero stable)
          (by
            have fits : ceilDiv (amount.toNat * wordModulusN)
                  (Nat.toB256 (denominatorN supply.toNat)).toNat < wordModulusN := by
              simpa [previewMintN, assetsMax, maxWord_toNat,
                assetFactorN_maxWord, stagedDenominator_toNat stable] using
                quoteFits
            simpa only [wideNumeratorN, B256.toNat_zero, Nat.add_zero] using
              fits)
          divideStack lookup divideRun
      exact ⟨mid, lift _ _ (divideLift _ _ divideSource), bodyRun⟩
    · obtain ⟨dividePre, divideStack, divideWf, divideReads, divideRun,
          divideLift⟩ :=
        mulDiv_split bodyWf bodyReads (ProducesWord.stagedDenominator supplyAt)
          (ProducesWord.amount_after_denominatorScratch amountAt)
          (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
          bodyStack armRun
      obtain ⟨mid, divideSource, bodyRun⟩ :=
        divide512_up_run divideWf divideReads
          (mulDivTraceImage_denominator _ _ _ _)
          (mulDivTraceImage_high _ _ _ _) (mulDivTraceImage_low _ _ _ _)
          (stagedDenominator_ne_zero stable)
          (by
            rw [wideNumeratorN_productWords]
            simpa [previewMintN, stagedDenominator_toNat stable,
              stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteFits)
          divideStack lookup divideRun
      exact ⟨mid, lift _ _ (divideLift _ _ divideSource), bodyRun⟩
  have stopLookup := Func.stopTable_get mintAfterQuoteSlot
  rcases ProducesWord.isMax_arm_trace (R := Func.Run)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack source with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    obtain ⟨-, quotePre, quoteImage, quoteStack, quoteMemImage, quoteFrame,
        quoteState, quoteRun⟩ :=
      shiftedDiv_up_image_trace armWf armReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, quoteImage, ?_, quoteMemImage, quoteFrame,
      armState.trans quoteState, bodyRun⟩
    simpa [previewMintN, assetsMax, maxWord_toNat, assetFactorN_maxWord,
      stagedDenominator_toNat stable] using quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    obtain ⟨-, quotePre, quoteImage, quoteStack, quoteMemImage, quoteFrame,
        quoteState, quoteRun⟩ :=
      mulDiv_up_image_trace armWf armReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, quoteImage, ?_, quoteMemImage, quoteFrame,
      armState.trans quoteState, bodyRun⟩
    simpa [previewMintN, stagedDenominator_toNat stable,
      stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack

/-- `withdraw`'s quote along an avoiding walk: the exact ceiling burn quote
reaches `withdrawAfterQuote` whenever it fits a word. -/
theorem withdrawQuote_avoiding {pre : Devm} {out : Execution}
    {image : Bytes} {amount assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (amountAt : Bytes.toB256
      (image.sliceD (amountWord * 32).toNat 32 0) = amount)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (lookup : fs[withdrawAfterQuoteSlot]? = some withdrawAfterQuote)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 (loadWord amountWord) stagedDenominator .up
            withdrawAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor
            .up withdrawAfterQuoteSlot)) out)
    (quoteFits : previewWithdrawN amount.toNat assets.toNat supply.toNat < wordModulusN) :
    ∃ bodyPre bodyImage,
      Nat.toB256 (previewWithdrawN amount.toNat assets.toNat supply.toNat) ::
        tail <<+ bodyPre.stack ∧
      MemImage bodyPre bodyImage ∧
      Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
      Devm.QuietFrame pre bodyPre ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre withdrawAfterQuote out := by
  obtain ⟨mid, source, bodyRun⟩ : ∃ mid,
      Func.Run (Func.stopTable withdrawAfterQuoteSlot) sevm pre
        (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 (loadWord amountWord) stagedDenominator .up
            withdrawAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor
            .up withdrawAfterQuoteSlot)) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid withdrawAfterQuote out := by
    rcases ProducesWord.isMax_split (ProducesWord.loadWord assetsAt) memoryWf
        memoryReads stack run with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, armRun, lift⟩ |
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, armRun, lift⟩
    · obtain ⟨mid, armSource, bodyRun⟩ :=
        productOverTwoPow256_up_run bodyWf bodyReads
          (ProducesWord.loadWord amountAt)
          (ProducesWord.stagedDenominator_after_productScratch supplyAt)
          (by
            simpa [previewWithdrawN, assetsMax, maxWord_toNat,
              assetFactorN_maxWord, stagedDenominator_toNat stable] using
              quoteFits)
          bodyStack lookup armRun
      exact ⟨mid, lift _ _ armSource, bodyRun⟩
    · obtain ⟨dividePre, divideStack, divideWf, divideReads, divideRun,
          divideLift⟩ :=
        mulDiv_split bodyWf bodyReads (ProducesWord.stagedAssetFactor assetsAt)
          (ProducesWord.amount_after_denominatorScratch amountAt)
          (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
          bodyStack armRun
      obtain ⟨mid, divideSource, bodyRun⟩ :=
        divide512_up_run divideWf divideReads
          (mulDivTraceImage_denominator _ _ _ _)
          (mulDivTraceImage_high _ _ _ _) (mulDivTraceImage_low _ _ _ _)
          (stagedAssetFactor_ne_zero assetsNotMax)
          (by
            rw [wideNumeratorN_productWords]
            simpa [previewWithdrawN, stagedDenominator_toNat stable,
              stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteFits)
          divideStack lookup divideRun
      exact ⟨mid, lift _ _ (divideLift _ _ divideSource), bodyRun⟩
  have stopLookup := Func.stopTable_get withdrawAfterQuoteSlot
  rcases ProducesWord.isMax_arm_trace (R := Func.Run)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack source with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨-, quotePre, quoteStack, quoteImage, quoteState, quoteRun⟩ :=
      productOverTwoPow256_up_image_trace armWf armReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, productOverTwoPow256TraceImage image amount denominator, ?_,
      quoteImage,
      productOverTwoPow256TraceImage_wordFrame image amount denominator,
      armState.trans quoteState, bodyRun⟩
    simpa [previewWithdrawN, denominator, assetsMax, maxWord_toNat,
      assetFactorN_maxWord, stagedDenominator_toNat stable] using quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    obtain ⟨-, quotePre, quoteImage, quoteStack, quoteMemImage, quoteFrame,
        quoteState, quoteRun⟩ :=
      mulDiv_up_image_trace armWf armReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, quoteImage, ?_, quoteMemImage, quoteFrame,
      armState.trans quoteState, bodyRun⟩
    simpa [previewWithdrawN, stagedDenominator_toNat stable,
      stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack

/-- `redeem`'s quote along an avoiding walk: the exact floor payout quote
reaches `redeemAfterQuote` whenever it fits a word. -/
theorem redeemQuote_avoiding {pre : Devm} {out : Execution}
    {image : Bytes} {amount assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (amountAt : Bytes.toB256
      (image.sliceD (amountWord * 32).toNat 32 0) = amount)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (lookup : fs[redeemAfterQuoteSlot]? = some redeemAfterQuote)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .down
            redeemAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .down redeemAfterQuoteSlot)) out)
    (quoteFits : previewRedeemN amount.toNat assets.toNat supply.toNat < wordModulusN) :
    ∃ bodyPre bodyImage,
      Nat.toB256 (previewRedeemN amount.toNat assets.toNat supply.toNat) ::
        tail <<+ bodyPre.stack ∧
      MemImage bodyPre bodyImage ∧
      Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
      Devm.QuietFrame pre bodyPre ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre redeemAfterQuote out := by
  obtain ⟨mid, source, bodyRun⟩ : ∃ mid,
      Func.Run (Func.stopTable redeemAfterQuoteSlot) sevm pre
        (loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .down
            redeemAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .down redeemAfterQuoteSlot)) mid ∧
      Func.RunCompiledToAvoiding P fs sevm mid redeemAfterQuote out := by
    rcases ProducesWord.isMax_split (ProducesWord.loadWord assetsAt) memoryWf
        memoryReads stack run with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, armRun, lift⟩ |
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, armRun, lift⟩
    · obtain ⟨dividePre, divideStack, divideWf, divideReads, divideRun,
          divideLift⟩ :=
        shiftedDiv_split bodyWf bodyReads (ProducesWord.loadWord amountAt)
          (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
          bodyStack armRun
      obtain ⟨mid, divideSource, bodyRun⟩ :=
        divide512_down_run (low := 0) divideWf divideReads
          (shiftedDivTraceImage_denominator _ _ _)
          (shiftedDivTraceImage_high _ _ _)
          (stagedDenominator_ne_zero stable)
          (by
            have fits : amount.toNat * wordModulusN /
                  (Nat.toB256 (denominatorN supply.toNat)).toNat < wordModulusN := by
              have h := quoteFits
              unfold previewRedeemN convertToAssetsN at h
              rw [assetsMax, maxWord_toNat, assetFactorN_maxWord] at h
              rw [stagedDenominator_toNat stable]
              exact h
            simpa only [wideNumeratorN, B256.toNat_zero, Nat.add_zero] using
              fits)
          divideStack lookup divideRun
      exact ⟨mid, lift _ _ (divideLift _ _ divideSource), bodyRun⟩
    · obtain ⟨dividePre, divideStack, divideWf, divideReads, divideRun,
          divideLift⟩ :=
        mulDiv_split bodyWf bodyReads (ProducesWord.stagedDenominator supplyAt)
          (ProducesWord.amount_after_denominatorScratch amountAt)
          (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
          bodyStack armRun
      obtain ⟨mid, divideSource, bodyRun⟩ :=
        divide512_down_run divideWf divideReads
          (mulDivTraceImage_denominator _ _ _ _)
          (mulDivTraceImage_high _ _ _ _)
          (stagedDenominator_ne_zero stable)
          (by
            rw [wideNumeratorN_productWords]
            simpa [previewRedeemN, convertToAssetsN, stagedDenominator_toNat stable,
              stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteFits)
          divideStack lookup divideRun
      exact ⟨mid, lift _ _ (divideLift _ _ divideSource), bodyRun⟩
  have stopLookup := Func.stopTable_get redeemAfterQuoteSlot
  rcases ProducesWord.isMax_arm_trace (R := Func.Run)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack source with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    obtain ⟨-, quotePre, quoteImage, quoteStack, quoteMemImage, quoteFrame,
        quoteState, quoteRun⟩ :=
      shiftedDiv_down_image_trace armWf armReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, quoteImage, ?_, quoteMemImage, quoteFrame,
      armState.trans quoteState, bodyRun⟩
    simpa [previewRedeemN, convertToAssetsN, assetsMax, maxWord_toNat,
      assetFactorN_maxWord, stagedDenominator_toNat stable] using quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, armPre, armStack, armWf, armReads, armState, armRun⟩
    obtain ⟨-, quotePre, quoteImage, quoteStack, quoteMemImage, quoteFrame,
        quoteState, quoteRun⟩ :=
      mulDiv_down_image_trace armWf armReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        armStack stopLookup armRun
    obtain rfl := Func.Run.stop_inv quoteRun
    refine ⟨mid, quoteImage, ?_, quoteMemImage, quoteFrame,
      armState.trans quoteState, bodyRun⟩
    simpa [previewRedeemN, convertToAssetsN, stagedDenominator_toNat stable,
      stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack

end

end ProrataWethVault

end Blanc
