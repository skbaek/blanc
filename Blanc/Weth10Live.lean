import Blanc.Forward
import Blanc.Weth10

/-! Call-free WETH10 view liveness at exact compiled-runtime altitude. -/

namespace Blanc
namespace Weth10

open Jaune
open Jaune.Ninst Ninst

/-! ## Selectors and independently authored gas sums -/

abbrev maxFlashLoanSel : B256 := selector "maxFlashLoan" [.address]
abbrev flashFeeSel : B256 := selector "flashFee" [.address, .uint256]
abbrev balanceOfSel : B256 := selector "balanceOf" [.address]
abbrev totalSupplySel : B256 := selector "totalSupply" []

/-! ## Default-limit dispatcher views

`func_run` must know the byte width of every `PUSH` on the selected path.
Reducing `leftmostFsig (weth10Tree dp)` inside the elaborator needlessly
normalizes the complete 27-leaf dispatcher.  The four views below expose only
one path with its independently pinned selector words; every off-path subtree
stays as the exact `dispatchWith` of the corresponding tree slice.  The
kernel-checked equalities following the views tie them back to `weth10 dp`. -/

private theorem totalSupplySel_eq :
    totalSupplySel = (0x18160ddd : B256) := by decide +kernel
private theorem withdrawToSel_eq :
    selector "withdrawTo" [.address, .uint256] =
      (0x205c2878 : B256) := by decide +kernel
private theorem transferFromSel_eq :
    selector "transferFrom" [.address, .address, .uint256] =
      (0x23b872dd : B256) := by decide +kernel
private theorem decimalsSel_eq :
    selector "decimals" [] = (0x313ce567 : B256) := by decide +kernel
private theorem depositToAndCallSel_eq :
    selector "depositToAndCall" [.address, .dynBytes] =
      (0x5ddb7d7e : B256) := by decide +kernel
private theorem maxFlashLoanSel_eq :
    maxFlashLoanSel = (0x613255ab : B256) := by decide +kernel
private theorem balanceOfSel_eq :
    balanceOfSel = (0x70a08231 : B256) := by decide +kernel
private theorem noncesSel_eq :
    selector "nonces" [.address] = (0x7ecebe00 : B256) := by decide +kernel
private theorem approveAndCallSel_eq :
    selector "approveAndCall" [.address, .uint256, .dynBytes] =
      (0xcae9ca51 : B256) := by decide +kernel
private theorem permitSel_eq :
    selector "permit"
        [.address, .address, .uint256, .uint256, .uint 8, .bytes 32, .bytes 32] =
      (0xd505accf : B256) := by decide +kernel
private theorem flashFeeSel_eq :
    flashFeeSel = (0xd9d98ce4 : B256) := by decide +kernel
private theorem allowanceSel_eq :
    selector "allowance" [.address, .address] =
      (0xdd62ed3e : B256) := by decide +kernel

private def treeSlice (dp : DeployParams) (fuel lo len : Nat) : DispatchTree :=
  DispatchTree.build fuel ((weth10Funcs dp).drop lo |>.take len)

private def dispatch26_14_13 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 26 14 13)
private def dispatch25_7_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 25 7 7)
private def dispatch24_4_3 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 24 4 3)
private def dispatch23_0_2 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 0 2)
private def dispatch22_3_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 22 3 1)
private def dispatch25_0_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 25 0 7)
private def dispatch24_7_4 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 24 7 4)
private def dispatch23_13_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 13 1)
private def dispatch22_11_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 22 11 1)
private def dispatch23_11_2 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 11 2)
private def dispatch26_0_14 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 26 0 14)
private def dispatch25_14_7 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 25 14 7)
private def dispatch24_21_3 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 24 21 3)
private def dispatch23_26_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 23 26 1)
private def dispatch22_24_1 (dp : DeployParams) : Func :=
  dispatchWith fallbackSlot (treeSlice dp 22 24 1)

private def totalSupplyDispatch (dp : DeployParams) : Func :=
  dup 0 ::: pushB256 (0x7ecebe00 : B256) ::: gt :::
  ((dup 0 ::: pushB256 (0x313ce567 : B256) ::: gt :::
    ((dup 0 ::: pushB256 (0x23b872dd : B256) ::: gt :::
      ((dup 0 ::: pushB256 (0x18160ddd : B256) ::: gt :::
        (dispatch23_0_2 dp <?>
          (dup 0 ::: pushB256 (0x205c2878 : B256) ::: gt :::
            ((pushB256 (0x18160ddd : B256) ::: eq :::
              ((nonpayable totalSupply) <?> .call fallbackSlot)) <?>
              dispatch22_3_1 dp)))) <?>
        dispatch24_4_3 dp)) <?>
    dispatch25_7_7 dp)) <?>
  dispatch26_14_13 dp)

private def maxFlashLoanDispatch (dp : DeployParams) : Func :=
  dup 0 ::: pushB256 (0x7ecebe00 : B256) ::: gt :::
  ((dup 0 ::: pushB256 (0x313ce567 : B256) ::: gt :::
    (dispatch25_0_7 dp <?>
      (dup 0 ::: pushB256 (0x5ddb7d7e : B256) ::: gt :::
        (dispatch24_7_4 dp <?>
          (dup 0 ::: pushB256 (0x70a08231 : B256) ::: gt :::
            ((dup 0 ::: pushB256 (0x613255ab : B256) ::: gt :::
              (dispatch22_11_1 dp <?>
                (pushB256 (0x613255ab : B256) ::: eq :::
                  ((nonpayable maxFlashLoan) <?> .call fallbackSlot)))) <?>
            dispatch23_13_1 dp)))))) <?>
  dispatch26_14_13 dp)

private def balanceOfDispatch (dp : DeployParams) : Func :=
  dup 0 ::: pushB256 (0x7ecebe00 : B256) ::: gt :::
  ((dup 0 ::: pushB256 (0x313ce567 : B256) ::: gt :::
    (dispatch25_0_7 dp <?>
      (dup 0 ::: pushB256 (0x5ddb7d7e : B256) ::: gt :::
        (dispatch24_7_4 dp <?>
          (dup 0 ::: pushB256 (0x70a08231 : B256) ::: gt :::
            (dispatch23_11_2 dp <?>
              (pushB256 (0x70a08231 : B256) ::: eq :::
                ((nonpayable balanceOfEndpoint) <?> .call fallbackSlot)))))))) <?>
  dispatch26_14_13 dp)

private def flashFeeDispatch (dp : DeployParams) : Func :=
  dup 0 ::: pushB256 (0x7ecebe00 : B256) ::: gt :::
  (dispatch26_0_14 dp <?>
    (dup 0 ::: pushB256 (0xcae9ca51 : B256) ::: gt :::
      (dispatch25_14_7 dp <?>
        (dup 0 ::: pushB256 (0xd505accf : B256) ::: gt :::
          (dispatch24_21_3 dp <?>
            (dup 0 ::: pushB256 (0xdd62ed3e : B256) ::: gt :::
              ((dup 0 ::: pushB256 (0xd9d98ce4 : B256) ::: gt :::
                (dispatch22_24_1 dp <?>
                  (pushB256 (0xd9d98ce4 : B256) ::: eq :::
                    ((nonpayable flashFee) <?> .call fallbackSlot)))) <?>
              dispatch23_26_1 dp)))))))

private theorem totalSupplyDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = totalSupplyDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    treeSlice, dispatch26_14_13, dispatch25_7_7, dispatch24_4_3,
    dispatch23_0_2, dispatch22_3_1, totalSupplyDispatch, dispatchWith,
    leftmostFsig,
    totalSupplySel_eq, withdrawToSel_eq, transferFromSel_eq, decimalsSel_eq,
    noncesSel_eq]

private theorem maxFlashLoanDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = maxFlashLoanDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    treeSlice, dispatch26_14_13, dispatch25_0_7, dispatch24_7_4,
    dispatch23_13_1, dispatch22_11_1, maxFlashLoanDispatch, dispatchWith,
    leftmostFsig,
    decimalsSel_eq, depositToAndCallSel_eq, maxFlashLoanSel_eq,
    balanceOfSel_eq, noncesSel_eq]

private theorem balanceOfDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = balanceOfDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    treeSlice, dispatch26_14_13, dispatch25_0_7, dispatch24_7_4,
    dispatch23_11_2, balanceOfDispatch, dispatchWith, leftmostFsig,
    decimalsSel_eq, depositToAndCallSel_eq, balanceOfSel_eq, noncesSel_eq]

private theorem flashFeeDispatch_eq (dp : DeployParams) :
    dispatchWith fallbackSlot (weth10Tree dp) = flashFeeDispatch dp := by
  simp [weth10Tree, DispatchTree.ofSorted, weth10Funcs, DispatchTree.build,
    treeSlice, dispatch26_0_14, dispatch25_14_7, dispatch24_21_3,
    dispatch23_26_1, dispatch22_24_1, flashFeeDispatch, dispatchWith,
    leftmostFsig,
    noncesSel_eq, approveAndCallSel_eq, permitSel_eq, flashFeeSel_eq,
    allowanceSel_eq]

private def totalSupplyMain (dp : DeployParams) : Func :=
  calldatasize ::: iszero :::
    (receiveEther <?> (fsig +++ totalSupplyDispatch dp))

private def maxFlashLoanMain (dp : DeployParams) : Func :=
  calldatasize ::: iszero :::
    (receiveEther <?> (fsig +++ maxFlashLoanDispatch dp))

private def balanceOfMain (dp : DeployParams) : Func :=
  calldatasize ::: iszero :::
    (receiveEther <?> (fsig +++ balanceOfDispatch dp))

private def flashFeeMain (dp : DeployParams) : Func :=
  calldatasize ::: iszero :::
    (receiveEther <?> (fsig +++ flashFeeDispatch dp))

private theorem weth10Main_eq_totalSupply (dp : DeployParams) :
    (weth10 dp).main = totalSupplyMain dp := by
  simp only [weth10, weth10Main, totalSupplyDispatch_eq, totalSupplyMain]

private theorem weth10Main_eq_maxFlashLoan (dp : DeployParams) :
    (weth10 dp).main = maxFlashLoanMain dp := by
  simp only [weth10, weth10Main, maxFlashLoanDispatch_eq, maxFlashLoanMain]

private theorem weth10Main_eq_balanceOf (dp : DeployParams) :
    (weth10 dp).main = balanceOfMain dp := by
  simp only [weth10, weth10Main, balanceOfDispatch_eq, balanceOfMain]

private theorem weth10Main_eq_flashFee (dp : DeployParams) :
    (weth10 dp).main = flashFeeMain dp := by
  simp only [weth10, weth10Main, flashFeeDispatch_eq, flashFeeMain]

private def branchGas (taken : Bool) : Nat :=
  gVerylow + gHigh + if taken then gJumpdest else 0

private def dispatchForkGas (taken : Bool) : Nat :=
  gVerylow + gVerylow + gVerylow + branchGas taken

/-- Entry `JUMPDEST`, nonempty-calldata guard, selector load, binary-search
forks, matching leaf, and the successful nonpayability guard. -/
private def viewDispatchGas (forks : List Bool) : Nat :=
  gJumpdest
    + (gBase + gVerylow + branchGas false)
    + (gBase + gVerylow + gVerylow + gVerylow)
    + (forks.map dispatchForkGas).sum
    + (gVerylow + gVerylow + branchGas true)
    + (gBase + gVerylow + branchGas true)

private def returnWordGas (push : Nat) : Nat :=
  push + (gBase + (gVerylow + gMemory)) + (gVerylow + gBase)

/-- Exact successful `flashFee(self, amount)` cost. The amount word is ignored. -/
def flashFeeGas : Nat :=
  viewDispatchGas [false, false, false, true, false]
    + (gVerylow + gVerylow)
    + gBase + gVerylow + gVerylow + branchGas false
    + returnWordGas gBase

theorem flashFeeGas_eq : flashFeeGas = 222 := by decide

/-- Exact `balanceOf` cost with the one storage-access charge abstracted. -/
def balanceOfGasWith (sload : Nat) : Nat :=
  viewDispatchGas [true, false, false, false]
    + (gVerylow + gVerylow + sload)
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

def balanceOfGasCold : Nat := balanceOfGasWith gasColdSload
def balanceOfGasWarm : Nat := balanceOfGasWith gasWarmAccess

theorem balanceOfGasCold_eq : balanceOfGasCold = 2277 := by decide
theorem balanceOfGasWarm_eq : balanceOfGasWarm = 277 := by decide

/-- Exact `totalSupply` cost with its `flashMinted` read abstracted. -/
def totalSupplyGasWith (sload : Nat) : Nat :=
  viewDispatchGas [true, true, true, false, true]
    + gLow + (gBase + gVerylow) + sload + gVerylow
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

def totalSupplyGasCold : Nat := totalSupplyGasWith gasColdSload
def totalSupplyGasWarm : Nat := totalSupplyGasWith gasWarmAccess

theorem totalSupplyGasCold_eq : totalSupplyGasCold = 2309 := by decide
theorem totalSupplyGasWarm_eq : totalSupplyGasWarm = 309 := by decide

/-- Exact self-token `maxFlashLoan` cost with its `flashMinted` read abstracted. -/
def maxFlashLoanGasWith (sload : Nat) : Nat :=
  viewDispatchGas [true, false, false, true, false]
    + (gVerylow + gVerylow) + gBase + gVerylow + branchGas true
    + (gBase + gVerylow) + sload + gVerylow + gVerylow
    + (gBase + (gVerylow + gMemory))
    + (gVerylow + gBase)

def maxFlashLoanGasCold : Nat := maxFlashLoanGasWith gasColdSload
def maxFlashLoanGasWarm : Nat := maxFlashLoanGasWith gasWarmAccess

/-- Exact non-self-token `maxFlashLoan` cost; this branch returns zero and does
not read `flashMinted`. -/
def maxFlashLoanOtherGas : Nat :=
  viewDispatchGas [true, false, false, true, false]
    + (gVerylow + gVerylow) + gBase + gVerylow + branchGas false
    + returnWordGas gBase

theorem maxFlashLoanGasCold_eq : maxFlashLoanGasCold = 2330 := by decide
theorem maxFlashLoanGasWarm_eq : maxFlashLoanGasWarm = 330 := by decide
theorem maxFlashLoanOtherGas_eq : maxFlashLoanOtherGas = 220 := by decide

private lemma gasLeft_withOutput {devm : Devm} {out : Bytes} :
    (devm.withOutput out).gasLeft = devm.gasLeft := rfl

private lemma gasLeft_memRead_snd {devm : Devm} {i sz : Nat} :
    (devm.memRead i sz).2.gasLeft = devm.gasLeft := rfl

/-! ## Contract-local body walks

The dispatcher and a cold storage body are checked separately.  This is the
same `Func.RunCompiled` derivation, composed at the exact residual function;
the split merely keeps the accessed-key successor from being normalized
through the whole dispatcher at once. -/

private def returnWordPre (base : Devm) (word : B256) (gas : Nat) : Devm :=
  base.setMach ⟨[], Mem.empty.write 0 word.toBytes, gas⟩

private theorem returnWord_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {word : B256}
    {g G : Nat} (h_gas : g = G + 5) :
    ∃ post,
      Func.RunCompiled fs sevm
        (returnWordPre base word g)
        (returnMemoryRange 0 32) post ∧
      post.gasLeft = G ∧
      Devm.output post = word.toBytes := by
  let M := Mem.empty.write 0 word.toBytes
  let retPre := base.setMach
    ⟨[(0 : B256), (32 : B256)], M, g - 5⟩
  let d := (retPre.setMach ⟨[], retPre.memory, g - 5⟩).memRead 0 32
  let post := d.2.withOutput word.toBytes
  refine ⟨post, ?_, ?_, ?_⟩
  · simp only [returnWordPre, returnMemoryRange, pushList]
    func_run (2) []
    simp only [List.map, prepend]
    change Func.RunCompiled fs sevm retPre Func.ret post
    have h_ext :
        retPre.extCost [⟨(0 : B256).toNat, (32 : B256).toNat⟩] = 0 := by
      change retPre.extCost [((0 : Nat), (32 : Nat))] = 0
      simpa only [retPre, M] using
        (Devm.extCost_word_word Mem.size_write_word)
    have h_read :
        (retPre.setMach ⟨[], retPre.memory, g - 5⟩).memRead 0 32 =
          ⟨word.toBytes, d.2⟩ := by
      exact Prod.ext
        (Devm.memRead_word_fst
          (by simp only [Devm.memory_setMach, retPre, M]))
        rfl
    exact Func.runCompiled_ret_of (devm := retPre) (G := g - 5) (e := 0)
      (out := word.toBytes) (d' := d.2) rfl h_ext
      (by simp only [retPre, Devm.gasLeft_setMach, Nat.add_zero])
      h_read
  · simp only [post, d, retPre, gasLeft_withOutput,
      gasLeft_memRead_snd, Devm.gasLeft_setMach]
    omega
  · rfl

private lemma addAccessedStorageKey_setMach_setMach {base : Devm}
    {m m' : Mach} {target : Adr} {key : B256} :
    (addAccessedStorageKey (base.setMach m) target key).setMach m' =
      (addAccessedStorageKey base target key).setMach m' := rfl

private def balanceOfBodyTail : Func :=
  [calldataload] +++ sload ::: mstoreAt 0 +++ returnMemoryRange 0 32

private theorem balanceOfBody_cold_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {g : Nat}
    (h_cold :
      (⟨sevm.currentTarget,
          Sevm.dataWord sevm (32 * 0 + 4)⟩ : Adr × B256) ∉
        base.accessedStorageKeys)
    (h_gas : 2116 ≤ g) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[(32 * 0 + 4 : B256)], Mem.empty, g⟩)
        balanceOfBodyTail post ∧
      post.gasLeft = g - 2116 ∧
      Devm.output post =
        (Devm.getStorVal base sevm.currentTarget
          (Sevm.dataWord sevm (32 * 0 + 4))).toBytes := by
  have h_cold_at_load :
      (⟨sevm.currentTarget,
          Sevm.dataWord sevm (32 * 0 + 4)⟩ : Adr × B256) ∉
        (base.setMach
          ⟨[Sevm.dataWord sevm (32 * 0 + 4)], Mem.empty,
            g - 3⟩).accessedStorageKeys := by
    exact h_cold
  have h_tail_gas : g - 2111 = (g - 2116) + 5 := by omega
  have h_push_gas : g - 2103 = g - 2105 + gBase := by
    change g - 2103 = g - 2105 + 2
    clear h_cold_at_load h_cold fs sevm base h_tail_gas
    omega
  have h_mstore_gas :
      g - 2105 = g - 2111 + (gVerylow + 3) := by
    change g - 2105 = g - 2111 + 6
    clear h_cold_at_load h_cold fs sevm base h_tail_gas h_push_gas
    omega
  rcases returnWord_runCompiled
      (fs := fs) (sevm := sevm)
      (base := addAccessedStorageKey base sevm.currentTarget
        (Sevm.dataWord sevm (32 * 0 + 4)))
      (word := Devm.getStorVal base sevm.currentTarget
        (Sevm.dataWord sevm (32 * 0 + 4)))
      h_tail_gas with ⟨post, h_tail, h_post_gas, h_out⟩
  refine ⟨post, ?_, h_post_gas, h_out⟩
  simp only [balanceOfBodyTail]
  refine Func.RunCompiled.next
    (devm' := base.setMach
      ⟨[Sevm.dataWord sevm (32 * 0 + 4)], Mem.empty, g - 3⟩) ?_ ?_
  · exact Ninst.runCompiled_calldataload (sevm := sevm) rfl rfl
      (by simp only [Devm.gasLeft_setMach, gVerylow]; omega) (by decide)
  · refine Func.RunCompiled.next
      (devm' :=
        (addAccessedStorageKey base sevm.currentTarget
          (Sevm.dataWord sevm (32 * 0 + 4))).setMach
        ⟨[Devm.getStorVal base sevm.currentTarget
            (Sevm.dataWord sevm (32 * 0 + 4))],
          Mem.empty, g - 2103⟩) ?_ ?_
    · simpa only [addAccessedStorageKey_setMach_setMach,
          Devm.getStorVal_setMach, Devm.memory_setMach] using
        (Ninst.runCompiled_sload_cold (sevm := sevm)
          (devm := base.setMach
            ⟨[Sevm.dataWord sevm (32 * 0 + 4)], Mem.empty, g - 3⟩)
          (k := Sevm.dataWord sevm (32 * 0 + 4))
          (v := Devm.getStorVal base sevm.currentTarget
            (Sevm.dataWord sevm (32 * 0 + 4)))
          (s := []) (G := g - 2103) rfl h_cold_at_load
          Devm.getStorVal_setMach
          (by simp only [Devm.gasLeft_setMach, gasColdSload]; omega)
          (by decide))
    · refine Func.RunCompiled.next
        (devm' :=
          (addAccessedStorageKey base sevm.currentTarget
            (Sevm.dataWord sevm (32 * 0 + 4))).setMach
          ⟨[(0 : B256),
              Devm.getStorVal base sevm.currentTarget
                (Sevm.dataWord sevm (32 * 0 + 4))],
            Mem.empty, g - 2105⟩) ?_ ?_
      · rw [show (0 * 32 : B256) = 0 by decide]
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach, Devm.gasLeft_setMach] using
          (Ninst.runCompiled_pushB256 (sevm := sevm)
            (devm :=
              (addAccessedStorageKey base sevm.currentTarget
                (Sevm.dataWord sevm (32 * 0 + 4))).setMach
              ⟨[Devm.getStorVal base sevm.currentTarget
                  (Sevm.dataWord sevm (32 * 0 + 4))],
                Mem.empty, g - 2103⟩)
            (w := 0) (c := gBase) (G := g - 2105) rfl
            (by
              change g - 2103 = g - 2105 + gBase
              exact h_push_gas)
            (by simp only [Devm.stack_setMach, List.length_cons,
                List.length_nil]; omega))
      · refine Func.RunCompiled.next
          (devm' := returnWordPre
      (addAccessedStorageKey base sevm.currentTarget
        (Sevm.dataWord sevm (32 * 0 + 4)))
      (Devm.getStorVal base sevm.currentTarget
        (Sevm.dataWord sevm (32 * 0 + 4)))
            (g - 2111)) ?_ h_tail
        simp only [returnWordPre]
        simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach, Devm.gasLeft_setMach] using
          (Ninst.runCompiled_mstore_of (sevm := sevm)
            (devm :=
              (addAccessedStorageKey base sevm.currentTarget
                (Sevm.dataWord sevm (32 * 0 + 4))).setMach
              ⟨[(0 : B256),
                  Devm.getStorVal base sevm.currentTarget
                    (Sevm.dataWord sevm (32 * 0 + 4))],
                Mem.empty, g - 2105⟩)
            (i := 0)
            (v := Devm.getStorVal base sevm.currentTarget
              (Sevm.dataWord sevm (32 * 0 + 4)))
            (s := []) (G := g - 2111) (e := 3)
            (M := Mem.empty.write 0
              (Devm.getStorVal base sevm.currentTarget
                (Sevm.dataWord sevm (32 * 0 + 4))).toBytes)
            rfl Devm.extCost_empty_word
            (by
              change g - 2105 = g - 2111 + (gVerylow + 3)
              exact h_mstore_gas)
            rfl)

private theorem totalSupplyBody_cold_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {g : Nat}
    (h_cold :
      (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∉
        base.accessedStorageKeys)
    (h_gas : 2126 ≤ g) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, g⟩) totalSupply post ∧
      post.gasLeft = g - 2126 ∧
      Devm.output post =
        (Devm.getStorVal base sevm.currentTarget flashMintedSlot +
          base.getBal sevm.currentTarget).toBytes := by
  have h_cold_at_load :
      (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∉
        (base.setMach
          ⟨[flashMintedSlot, base.getBal sevm.currentTarget], Mem.empty,
            g - 10⟩).accessedStorageKeys := h_cold
  have h_self_gas : g = g - 5 + gLow := by
    change g = g - 5 + 5
    clear h_cold_at_load h_cold fs sevm base
    omega
  have h_slot_push_gas : g - 5 = g - 7 + gBase := by
    change g - 5 = g - 7 + 2
    clear h_cold_at_load h_cold fs sevm base h_self_gas
    omega
  have h_not_gas : g - 7 = g - 10 + gVerylow := by
    change g - 7 = g - 10 + 3
    clear h_cold_at_load h_cold fs sevm base h_self_gas h_slot_push_gas
    omega
  have h_sload_gas : g - 10 = g - 2110 + gasColdSload := by
    change g - 10 = g - 2110 + 2100
    clear h_cold_at_load h_cold fs sevm base h_self_gas h_slot_push_gas
      h_not_gas
    omega
  have h_add_gas : g - 2110 = g - 2113 + gVerylow := by
    change g - 2110 = g - 2113 + 3
    clear h_cold_at_load h_cold fs sevm base h_self_gas h_slot_push_gas
      h_not_gas h_sload_gas
    omega
  have h_mstore_push_gas : g - 2113 = g - 2115 + gBase := by
    change g - 2113 = g - 2115 + 2
    clear h_cold_at_load h_cold fs sevm base h_self_gas h_slot_push_gas
      h_not_gas h_sload_gas h_add_gas
    omega
  have h_mstore_gas : g - 2115 = g - 2121 + (gVerylow + 3) := by
    change g - 2115 = g - 2121 + 6
    clear h_cold_at_load h_cold fs sevm base h_self_gas h_slot_push_gas
      h_not_gas h_sload_gas h_add_gas h_mstore_push_gas
    omega
  have h_tail_gas : g - 2121 = (g - 2126) + 5 := by
    clear h_cold_at_load h_cold fs sevm base h_self_gas h_slot_push_gas
      h_not_gas h_sload_gas h_add_gas h_mstore_push_gas h_mstore_gas
    omega
  rcases returnWord_runCompiled
      (fs := fs) (sevm := sevm)
      (base := addAccessedStorageKey base sevm.currentTarget flashMintedSlot)
      (word := Devm.getStorVal base sevm.currentTarget flashMintedSlot +
        base.getBal sevm.currentTarget)
      h_tail_gas with ⟨post, h_tail, h_post_gas, h_out⟩
  refine ⟨post, ?_, h_post_gas, h_out⟩
  simp only [totalSupply, pushFlashMintedSlot]
  refine Func.RunCompiled.next
    (devm' := base.setMach
      ⟨[base.getBal sevm.currentTarget], Mem.empty, g - 5⟩) ?_ ?_
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach] using
      (Ninst.runCompiled_pushItem (sevm := sevm)
        (devm := base.setMach ⟨[], Mem.empty, g⟩)
        (r := .selfbalance) (x := base.getBal sevm.currentTarget)
        (cost := gLow) (G := g - 5) (by rintro ⟨⟩) rfl
        (by
          change g = g - 5 + gLow
          exact h_self_gas)
        (by simp only [Devm.stack_setMach, List.length_nil]; omega))
  · refine Func.RunCompiled.next
      (devm' := base.setMach
        ⟨[(0 : B256), base.getBal sevm.currentTarget], Mem.empty,
          g - 7⟩) ?_ ?_
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach] using
        (Ninst.runCompiled_pushB256 (sevm := sevm)
          (devm := base.setMach
            ⟨[base.getBal sevm.currentTarget], Mem.empty, g - 5⟩)
          (w := 0) (c := gBase) (G := g - 7) rfl
          (by
            change g - 5 = g - 7 + gBase
            exact h_slot_push_gas)
          (by simp only [Devm.stack_setMach, List.length_cons,
              List.length_nil]; omega))
    · refine Func.RunCompiled.next
        (devm' := base.setMach
          ⟨[flashMintedSlot, base.getBal sevm.currentTarget], Mem.empty,
            g - 10⟩) ?_ ?_
      · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
            Devm.memory_setMach, Devm.gasLeft_setMach] using
          (Ninst.runCompiled_unary (sevm := sevm)
            (devm := base.setMach
              ⟨[(0 : B256), base.getBal sevm.currentTarget], Mem.empty,
                g - 7⟩)
            (r := .not) (f := (~~~ ·)) (cost := gVerylow)
            (x := 0) (v := flashMintedSlot)
            (s := [base.getBal sevm.currentTarget]) (G := g - 10)
            (by rintro ⟨⟩) rfl rfl rfl
            (by
              change g - 7 = g - 10 + gVerylow
              exact h_not_gas)
            (by simp only [List.length_cons, List.length_nil]; omega))
      · refine Func.RunCompiled.next
          (devm' :=
            (addAccessedStorageKey base sevm.currentTarget flashMintedSlot).setMach
              ⟨[Devm.getStorVal base sevm.currentTarget flashMintedSlot,
                  base.getBal sevm.currentTarget],
                Mem.empty, g - 2110⟩) ?_ ?_
        · simpa only [addAccessedStorageKey_setMach_setMach,
              Devm.getStorVal_setMach, Devm.memory_setMach] using
            (Ninst.runCompiled_sload_cold (sevm := sevm)
              (devm := base.setMach
                ⟨[flashMintedSlot, base.getBal sevm.currentTarget],
                  Mem.empty, g - 10⟩)
              (k := flashMintedSlot)
              (v := Devm.getStorVal base sevm.currentTarget flashMintedSlot)
              (s := [base.getBal sevm.currentTarget]) (G := g - 2110)
              rfl h_cold_at_load Devm.getStorVal_setMach
              (by
                simp only [Devm.gasLeft_setMach]
                exact h_sload_gas)
              (by simp only [List.length_cons, List.length_nil]; omega))
        · refine Func.RunCompiled.next
            (devm' :=
              (addAccessedStorageKey base sevm.currentTarget flashMintedSlot).setMach
                ⟨[Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                    base.getBal sevm.currentTarget],
                  Mem.empty, g - 2113⟩) ?_ ?_
          · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
                Devm.memory_setMach, Devm.gasLeft_setMach] using
              (Ninst.runCompiled_binary (sevm := sevm)
                (devm :=
                  (addAccessedStorageKey base sevm.currentTarget
                    flashMintedSlot).setMach
                    ⟨[Devm.getStorVal base sevm.currentTarget flashMintedSlot,
                        base.getBal sevm.currentTarget],
                      Mem.empty, g - 2110⟩)
                (r := .add) (f := (· + ·)) (cost := gVerylow)
                (x := Devm.getStorVal base sevm.currentTarget flashMintedSlot)
                (y := base.getBal sevm.currentTarget)
                (v := Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                  base.getBal sevm.currentTarget)
                (s := []) (G := g - 2113)
                (by rintro ⟨⟩) rfl rfl rfl
                (by
                  change g - 2110 = g - 2113 + gVerylow
                  exact h_add_gas)
                (by decide))
          · refine Func.RunCompiled.next
              (devm' :=
                (addAccessedStorageKey base sevm.currentTarget flashMintedSlot).setMach
                  ⟨[(0 : B256),
                      Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                        base.getBal sevm.currentTarget],
                    Mem.empty, g - 2115⟩) ?_ ?_
            · rw [show (0 * 32 : B256) = 0 by decide]
              simpa only [Devm.setMach_setMach, Devm.stack_setMach,
                    Devm.memory_setMach, Devm.gasLeft_setMach] using
                (Ninst.runCompiled_pushB256 (sevm := sevm)
                  (devm :=
                    (addAccessedStorageKey base sevm.currentTarget
                      flashMintedSlot).setMach
                      ⟨[Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                          base.getBal sevm.currentTarget],
                        Mem.empty, g - 2113⟩)
                  (w := 0) (c := gBase) (G := g - 2115) rfl
                  (by
                    change g - 2113 = g - 2115 + gBase
                    exact h_mstore_push_gas)
                  (by simp only [Devm.stack_setMach, List.length_cons,
                      List.length_nil]; omega))
            · refine Func.RunCompiled.next
                (devm' := returnWordPre
                  (addAccessedStorageKey base sevm.currentTarget flashMintedSlot)
                  (Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                    base.getBal sevm.currentTarget)
                  (g - 2121)) ?_ h_tail
              simp only [returnWordPre]
              simpa only [Devm.setMach_setMach, Devm.stack_setMach,
                  Devm.memory_setMach, Devm.gasLeft_setMach] using
                (Ninst.runCompiled_mstore_of (sevm := sevm)
                  (devm :=
                    (addAccessedStorageKey base sevm.currentTarget
                      flashMintedSlot).setMach
                      ⟨[(0 : B256),
                          Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                            base.getBal sevm.currentTarget],
                        Mem.empty, g - 2115⟩)
                  (i := 0)
                  (v := Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                    base.getBal sevm.currentTarget)
                  (s := []) (G := g - 2121) (e := 3)
                  (M := Mem.empty.write 0
                    (Devm.getStorVal base sevm.currentTarget flashMintedSlot +
                      base.getBal sevm.currentTarget).toBytes)
                  rfl Devm.extCost_empty_word
                  (by
                    change g - 2115 = g - 2121 + (gVerylow + 3)
                    exact h_mstore_gas)
                  rfl)

private def maxFlashLoanSelfBody : Func :=
  pushFlashMintedSlot +++ sload :::
    pushB256 (Nat.toB256 maxFlashMinted) ::: sub :::
    mstoreAt 0 +++ returnMemoryRange 0 32

private theorem maxFlashLoanSelfBody_cold_runCompiled
    {fs : List Func} {sevm : Sevm} {base : Devm} {g : Nat}
    (h_cold :
      (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∉
        base.accessedStorageKeys)
    (h_gas : 2124 ≤ g) :
    ∃ post,
      Func.RunCompiled fs sevm
        (base.setMach ⟨[], Mem.empty, g⟩) maxFlashLoanSelfBody post ∧
      post.gasLeft = g - 2124 ∧
      Devm.output post =
        (Nat.toB256 maxFlashMinted -
          Devm.getStorVal base sevm.currentTarget flashMintedSlot).toBytes := by
  have h_cold_at_load :
      (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∉
        (base.setMach ⟨[flashMintedSlot], Mem.empty, g - 5⟩).accessedStorageKeys :=
    h_cold
  have h_slot_push_gas : g = g - 2 + gBase := by
    change g = g - 2 + 2
    clear h_cold_at_load h_cold fs sevm base
    omega
  have h_not_gas : g - 2 = g - 5 + gVerylow := by
    change g - 2 = g - 5 + 3
    clear h_cold_at_load h_cold fs sevm base h_slot_push_gas
    omega
  have h_sload_gas : g - 5 = g - 2105 + gasColdSload := by
    change g - 5 = g - 2105 + 2100
    clear h_cold_at_load h_cold fs sevm base h_slot_push_gas h_not_gas
    omega
  have h_max_push_gas : g - 2105 = g - 2108 + gVerylow := by
    change g - 2105 = g - 2108 + 3
    clear h_cold_at_load h_cold fs sevm base h_slot_push_gas h_not_gas
      h_sload_gas
    omega
  have h_sub_gas : g - 2108 = g - 2111 + gVerylow := by
    change g - 2108 = g - 2111 + 3
    clear h_cold_at_load h_cold fs sevm base h_slot_push_gas h_not_gas
      h_sload_gas h_max_push_gas
    omega
  have h_mstore_push_gas : g - 2111 = g - 2113 + gBase := by
    change g - 2111 = g - 2113 + 2
    clear h_cold_at_load h_cold fs sevm base h_slot_push_gas h_not_gas
      h_sload_gas h_max_push_gas h_sub_gas
    omega
  have h_mstore_gas : g - 2113 = g - 2119 + (gVerylow + 3) := by
    change g - 2113 = g - 2119 + 6
    clear h_cold_at_load h_cold fs sevm base h_slot_push_gas h_not_gas
      h_sload_gas h_max_push_gas h_sub_gas h_mstore_push_gas
    omega
  have h_tail_gas : g - 2119 = (g - 2124) + 5 := by
    clear h_cold_at_load h_cold fs sevm base h_slot_push_gas h_not_gas
      h_sload_gas h_max_push_gas h_sub_gas h_mstore_push_gas h_mstore_gas
    omega
  rcases returnWord_runCompiled
      (fs := fs) (sevm := sevm)
      (base := addAccessedStorageKey base sevm.currentTarget flashMintedSlot)
      (word := Nat.toB256 maxFlashMinted -
        Devm.getStorVal base sevm.currentTarget flashMintedSlot)
      h_tail_gas with ⟨post, h_tail, h_post_gas, h_out⟩
  refine ⟨post, ?_, h_post_gas, h_out⟩
  simp only [maxFlashLoanSelfBody, pushFlashMintedSlot]
  refine Func.RunCompiled.next
    (devm' := base.setMach ⟨[(0 : B256)], Mem.empty, g - 2⟩) ?_ ?_
  · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
        Devm.memory_setMach, Devm.gasLeft_setMach] using
      (Ninst.runCompiled_pushB256 (sevm := sevm)
        (devm := base.setMach ⟨[], Mem.empty, g⟩)
        (w := 0) (c := gBase) (G := g - 2) rfl
        (by
          change g = g - 2 + gBase
          exact h_slot_push_gas)
        (by simp only [Devm.stack_setMach, List.length_nil]; omega))
  · refine Func.RunCompiled.next
      (devm' := base.setMach ⟨[flashMintedSlot], Mem.empty, g - 5⟩) ?_ ?_
    · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
          Devm.memory_setMach, Devm.gasLeft_setMach] using
        (Ninst.runCompiled_unary (sevm := sevm)
          (devm := base.setMach ⟨[(0 : B256)], Mem.empty, g - 2⟩)
          (r := .not) (f := (~~~ ·)) (cost := gVerylow)
          (x := 0) (v := flashMintedSlot) (s := []) (G := g - 5)
          (by rintro ⟨⟩) rfl rfl rfl
          (by
            change g - 2 = g - 5 + gVerylow
            exact h_not_gas)
          (by decide))
    · refine Func.RunCompiled.next
        (devm' :=
          (addAccessedStorageKey base sevm.currentTarget flashMintedSlot).setMach
            ⟨[Devm.getStorVal base sevm.currentTarget flashMintedSlot],
              Mem.empty, g - 2105⟩) ?_ ?_
      · simpa only [addAccessedStorageKey_setMach_setMach,
            Devm.getStorVal_setMach, Devm.memory_setMach] using
          (Ninst.runCompiled_sload_cold (sevm := sevm)
            (devm := base.setMach ⟨[flashMintedSlot], Mem.empty, g - 5⟩)
            (k := flashMintedSlot)
            (v := Devm.getStorVal base sevm.currentTarget flashMintedSlot)
            (s := []) (G := g - 2105) rfl h_cold_at_load
            Devm.getStorVal_setMach
            (by
              simp only [Devm.gasLeft_setMach]
              exact h_sload_gas)
            (by decide))
      · refine Func.RunCompiled.next
          (devm' :=
            (addAccessedStorageKey base sevm.currentTarget flashMintedSlot).setMach
              ⟨[Nat.toB256 maxFlashMinted,
                  Devm.getStorVal base sevm.currentTarget flashMintedSlot],
                Mem.empty, g - 2108⟩) ?_ ?_
        · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
              Devm.memory_setMach, Devm.gasLeft_setMach] using
            (Ninst.runCompiled_pushB256 (sevm := sevm)
              (devm :=
                (addAccessedStorageKey base sevm.currentTarget
                  flashMintedSlot).setMach
                  ⟨[Devm.getStorVal base sevm.currentTarget flashMintedSlot],
                    Mem.empty, g - 2105⟩)
              (w := Nat.toB256 maxFlashMinted) (c := gVerylow)
              (G := g - 2108) rfl
              (by
                change g - 2105 = g - 2108 + gVerylow
                exact h_max_push_gas)
              (by simp only [Devm.stack_setMach, List.length_cons,
                  List.length_nil]; omega))
        · refine Func.RunCompiled.next
            (devm' :=
              (addAccessedStorageKey base sevm.currentTarget flashMintedSlot).setMach
                ⟨[Nat.toB256 maxFlashMinted -
                    Devm.getStorVal base sevm.currentTarget flashMintedSlot],
                  Mem.empty, g - 2111⟩) ?_ ?_
          · simpa only [Devm.setMach_setMach, Devm.stack_setMach,
                Devm.memory_setMach, Devm.gasLeft_setMach] using
              (Ninst.runCompiled_binary (sevm := sevm)
                (devm :=
                  (addAccessedStorageKey base sevm.currentTarget
                    flashMintedSlot).setMach
                    ⟨[Nat.toB256 maxFlashMinted,
                        Devm.getStorVal base sevm.currentTarget flashMintedSlot],
                      Mem.empty, g - 2108⟩)
                (r := .sub) (f := (· - ·)) (cost := gVerylow)
                (x := Nat.toB256 maxFlashMinted)
                (y := Devm.getStorVal base sevm.currentTarget flashMintedSlot)
                (v := Nat.toB256 maxFlashMinted -
                  Devm.getStorVal base sevm.currentTarget flashMintedSlot)
                (s := []) (G := g - 2111)
                (by rintro ⟨⟩) rfl rfl rfl
                (by
                  change g - 2108 = g - 2111 + gVerylow
                  exact h_sub_gas)
                (by decide))
          · refine Func.RunCompiled.next
              (devm' :=
                (addAccessedStorageKey base sevm.currentTarget flashMintedSlot).setMach
                  ⟨[(0 : B256), Nat.toB256 maxFlashMinted -
                      Devm.getStorVal base sevm.currentTarget flashMintedSlot],
                    Mem.empty, g - 2113⟩) ?_ ?_
            · rw [show (0 * 32 : B256) = 0 by decide]
              simpa only [Devm.setMach_setMach, Devm.stack_setMach,
                    Devm.memory_setMach, Devm.gasLeft_setMach] using
                (Ninst.runCompiled_pushB256 (sevm := sevm)
                  (devm :=
                    (addAccessedStorageKey base sevm.currentTarget
                      flashMintedSlot).setMach
                      ⟨[Nat.toB256 maxFlashMinted -
                          Devm.getStorVal base sevm.currentTarget flashMintedSlot],
                        Mem.empty, g - 2111⟩)
                  (w := 0) (c := gBase) (G := g - 2113) rfl
                  (by
                    change g - 2111 = g - 2113 + gBase
                    exact h_mstore_push_gas)
                  (by simp only [Devm.stack_setMach, List.length_cons,
                      List.length_nil]; omega))
            · refine Func.RunCompiled.next
                (devm' := returnWordPre
                  (addAccessedStorageKey base sevm.currentTarget flashMintedSlot)
                  (Nat.toB256 maxFlashMinted -
                    Devm.getStorVal base sevm.currentTarget flashMintedSlot)
                  (g - 2119)) ?_ h_tail
              simp only [returnWordPre]
              simpa only [Devm.setMach_setMach, Devm.stack_setMach,
                  Devm.memory_setMach, Devm.gasLeft_setMach] using
                (Ninst.runCompiled_mstore_of (sevm := sevm)
                  (devm :=
                    (addAccessedStorageKey base sevm.currentTarget
                      flashMintedSlot).setMach
                      ⟨[(0 : B256), Nat.toB256 maxFlashMinted -
                          Devm.getStorVal base sevm.currentTarget flashMintedSlot],
                        Mem.empty, g - 2113⟩)
                  (i := 0)
                  (v := Nat.toB256 maxFlashMinted -
                    Devm.getStorVal base sevm.currentTarget flashMintedSlot)
                  (s := []) (G := g - 2119) (e := 3)
                  (M := Mem.empty.write 0
                    (Nat.toB256 maxFlashMinted -
                      Devm.getStorVal base sevm.currentTarget
                        flashMintedSlot).toBytes)
                  rfl Devm.extCost_empty_word
                  (by
                    change g - 2113 = g - 2119 + (gVerylow + 3)
                    exact h_mstore_gas)
                  rfl)

/-! ## Gas-exact compiled walks -/

/-- A valid `flashFee(self, amount)` call reaches the successful zero-return
branch for every deployment parameter pair. -/
theorem flashFee_runCompiled (dp : DeployParams) {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_token : Sevm.dataWord sevm 4 = sevm.currentTarget.toB256)
    (h_sel : Sevm.selector sevm = flashFeeSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : flashFeeGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + flashFeeGas = pre.gasLeft ∧
      Devm.output post = (0 : B256).toBytes := by
  rw [flashFeeSel_eq] at h_sel
  rw [flashFeeGas_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0xd9d98ce4 : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_token_eq :
              B256.eqCheck sevm.currentTarget.toB256
                (Sevm.dataWord sevm 4) = 1 := by
            simp [B256.eqCheck, h_token]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0xd9d98ce4 = 0 := by decide
          have h_fork1 :
              B256.gtCheck (0xcae9ca51 : B256) 0xd9d98ce4 = 0 := by decide
          have h_fork2 :
              B256.gtCheck (0xd505accf : B256) 0xd9d98ce4 = 0 := by decide
          have h_fork3 :
              B256.gtCheck (0xdd62ed3e : B256) 0xd9d98ce4 = 1 := by decide
          have h_fork4 :
              B256.gtCheck (0xd9d98ce4 : B256) 0xd9d98ce4 = 0 := by decide
          have h_leaf :
              B256.eqCheck (0xd9d98ce4 : B256) 0xd9d98ce4 = 1 := by decide
          rw [weth10Main_eq_flashFee]
          func_run [0, (0xd9d98ce4 : B256), 0, 0, 0, 1, 0, 1, 1, 1, 0, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 222) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst
                (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [gasLeft_withOutput, gasLeft_memRead_snd,
    Devm.gasLeft_setMach, flashFeeGas_eq]
  omega

/-- Cold-key `balanceOf` walk and exact raw-balance return. -/
theorem balanceOf_cold_runCompiled (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = balanceOfSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256) ∉
      pre.accessedStorageKeys)
    (h_gas : balanceOfGasCold ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + balanceOfGasCold = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget
          (Sevm.dataWord sevm 4)).toBytes := by
  rw [balanceOfSel_eq] at h_sel
  rw [balanceOfGasCold_eq] at h_gas
  set g := pre.gasLeft with hg
  have h_body_gas : 2116 ≤ g - 161 := by omega
  rcases balanceOfBody_cold_runCompiled
      (fs := balanceOfMain dp :: (weth10 dp).aux)
      (sevm := sevm) (base := pre) (g := g - 161)
      h_cold h_body_gas with ⟨post, h_body, h_post_gas, h_out⟩
  refine
    ⟨post,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0x70a08231 : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0x70a08231 = 1 := by decide
          have h_fork1 :
              B256.gtCheck (0x313ce567 : B256) 0x70a08231 = 0 := by decide
          have h_fork2 :
              B256.gtCheck (0x5ddb7d7e : B256) 0x70a08231 = 0 := by decide
          have h_fork3 :
              B256.gtCheck (0x70a08231 : B256) 0x70a08231 = 0 := by decide
          have h_leaf :
              B256.eqCheck (0x70a08231 : B256) 0x70a08231 = 1 := by decide
          rw [weth10Main_eq_balanceOf]
          func_run (30) [0, (0x70a08231 : B256), 1, 0, 0, 0, 1, 1]
          exact h_body),
      ?_, h_out⟩
  rw [h_post_gas, balanceOfGasCold_eq]
  omega

/-- Warm-key `balanceOf` walk and exact raw-balance return. -/
theorem balanceOf_warm_runCompiled (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = balanceOfSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_warm : (⟨sevm.currentTarget, Sevm.dataWord sevm 4⟩ : Adr × B256) ∈
      pre.accessedStorageKeys)
    (h_gas : balanceOfGasWarm ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + balanceOfGasWarm = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget
          (Sevm.dataWord sevm 4)).toBytes := by
  rw [balanceOfSel_eq] at h_sel
  rw [balanceOfGasWarm_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0x70a08231 : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0x70a08231 = 1 := by decide
          have h_fork1 :
              B256.gtCheck (0x313ce567 : B256) 0x70a08231 = 0 := by decide
          have h_fork2 :
              B256.gtCheck (0x5ddb7d7e : B256) 0x70a08231 = 0 := by decide
          have h_fork3 :
              B256.gtCheck (0x70a08231 : B256) 0x70a08231 = 0 := by decide
          have h_leaf :
              B256.eqCheck (0x70a08231 : B256) 0x70a08231 = 1 := by decide
          rw [weth10Main_eq_balanceOf]
          func_run [0, (0x70a08231 : B256), 1, 0, 0, 0, 1, 1, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 277) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst
                (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [gasLeft_withOutput, gasLeft_memRead_snd,
    Devm.gasLeft_setMach, balanceOfGasWarm_eq]
  omega

/-- Cold-key total-supply walk, including SELFBALANCE and flashMinted. -/
theorem totalSupply_cold_runCompiled (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = totalSupplySel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∉
      pre.accessedStorageKeys)
    (h_gas : totalSupplyGasCold ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + totalSupplyGasCold = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget flashMintedSlot +
          pre.getBal sevm.currentTarget).toBytes := by
  rw [totalSupplySel_eq] at h_sel
  rw [totalSupplyGasCold_eq] at h_gas
  set g := pre.gasLeft with hg
  have h_body_gas : 2126 ≤ g - 183 := by omega
  rcases totalSupplyBody_cold_runCompiled
      (fs := totalSupplyMain dp :: (weth10 dp).aux)
      (sevm := sevm) (base := pre) (g := g - 183)
      h_cold h_body_gas with ⟨post, h_body, h_post_gas, h_out⟩
  refine
    ⟨post,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0x18160ddd : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0x18160ddd = 1 := by decide
          have h_fork1 :
              B256.gtCheck (0x313ce567 : B256) 0x18160ddd = 1 := by decide
          have h_fork2 :
              B256.gtCheck (0x23b872dd : B256) 0x18160ddd = 1 := by decide
          have h_fork3 :
              B256.gtCheck (0x18160ddd : B256) 0x18160ddd = 0 := by decide
          have h_fork4 :
              B256.gtCheck (0x205c2878 : B256) 0x18160ddd = 1 := by decide
          have h_leaf :
              B256.eqCheck (0x18160ddd : B256) 0x18160ddd = 1 := by decide
          rw [weth10Main_eq_totalSupply]
          func_run (33) [0, (0x18160ddd : B256), 1, 1, 1, 0, 1, 1, 1]
          exact h_body),
      ?_, h_out⟩
  rw [h_post_gas, totalSupplyGasCold_eq]
  omega

/-- Warm-key total-supply walk, including SELFBALANCE and flashMinted. -/
theorem totalSupply_warm_runCompiled (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_sel : Sevm.selector sevm = totalSupplySel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_warm : (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∈
      pre.accessedStorageKeys)
    (h_gas : totalSupplyGasWarm ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + totalSupplyGasWarm = pre.gasLeft ∧
      Devm.output post =
        (Devm.getStorVal pre sevm.currentTarget flashMintedSlot +
          pre.getBal sevm.currentTarget).toBytes := by
  rw [totalSupplySel_eq] at h_sel
  rw [totalSupplyGasWarm_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0x18160ddd : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0x18160ddd = 1 := by decide
          have h_fork1 :
              B256.gtCheck (0x313ce567 : B256) 0x18160ddd = 1 := by decide
          have h_fork2 :
              B256.gtCheck (0x23b872dd : B256) 0x18160ddd = 1 := by decide
          have h_fork3 :
              B256.gtCheck (0x18160ddd : B256) 0x18160ddd = 0 := by decide
          have h_fork4 :
              B256.gtCheck (0x205c2878 : B256) 0x18160ddd = 1 := by decide
          have h_leaf :
              B256.eqCheck (0x18160ddd : B256) 0x18160ddd = 1 := by decide
          rw [weth10Main_eq_totalSupply]
          func_run [0, (0x18160ddd : B256), 1, 1, 1, 0, 1, 1, 1,
            flashMintedSlot,
            Devm.getStorVal pre sevm.currentTarget flashMintedSlot +
              pre.getBal sevm.currentTarget,
            3]
          · simp only [Devm.gasLeft_setMach, gLow]
            omega
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 309) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst
                (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [gasLeft_withOutput, gasLeft_memRead_snd,
    Devm.gasLeft_setMach, totalSupplyGasWarm_eq]
  omega

/-- Cold-key self-token `maxFlashLoan` walk and exact remaining capacity. -/
theorem maxFlashLoan_cold_runCompiled (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_token : Sevm.dataWord sevm 4 = sevm.currentTarget.toB256)
    (h_sel : Sevm.selector sevm = maxFlashLoanSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_cold : (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∉
      pre.accessedStorageKeys)
    (h_gas : maxFlashLoanGasCold ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + maxFlashLoanGasCold = pre.gasLeft ∧
      Devm.output post =
        (Nat.toB256 maxFlashMinted -
          Devm.getStorVal pre sevm.currentTarget flashMintedSlot).toBytes := by
  rw [maxFlashLoanSel_eq] at h_sel
  rw [maxFlashLoanGasCold_eq] at h_gas
  set g := pre.gasLeft with hg
  have h_body_gas : 2124 ≤ g - 206 := by omega
  rcases maxFlashLoanSelfBody_cold_runCompiled
      (fs := maxFlashLoanMain dp :: (weth10 dp).aux)
      (sevm := sevm) (base := pre) (g := g - 206)
      h_cold h_body_gas with ⟨post, h_body, h_post_gas, h_out⟩
  refine
    ⟨post,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0x613255ab : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_token_eq :
              B256.eqCheck sevm.currentTarget.toB256
                (Sevm.dataWord sevm 4) = 1 := by
            simp [B256.eqCheck, h_token]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0x613255ab = 1 := by decide
          have h_fork1 :
              B256.gtCheck (0x313ce567 : B256) 0x613255ab = 0 := by decide
          have h_fork2 :
              B256.gtCheck (0x5ddb7d7e : B256) 0x613255ab = 0 := by decide
          have h_fork3 :
              B256.gtCheck (0x70a08231 : B256) 0x613255ab = 1 := by decide
          have h_fork4 :
              B256.gtCheck (0x613255ab : B256) 0x613255ab = 0 := by decide
          have h_leaf :
              B256.eqCheck (0x613255ab : B256) 0x613255ab = 1 := by decide
          rw [weth10Main_eq_maxFlashLoan]
          func_run (38) [0, (0x613255ab : B256), 1, 0, 0, 1, 0, 1, 1, 1]
          simpa only [maxFlashLoanSelfBody] using h_body),
      ?_, h_out⟩
  rw [h_post_gas, maxFlashLoanGasCold_eq]
  omega

/-- Warm-key self-token `maxFlashLoan` walk and exact remaining capacity. -/
theorem maxFlashLoan_warm_runCompiled (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_token : Sevm.dataWord sevm 4 = sevm.currentTarget.toB256)
    (h_sel : Sevm.selector sevm = maxFlashLoanSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_warm : (⟨sevm.currentTarget, flashMintedSlot⟩ : Adr × B256) ∈
      pre.accessedStorageKeys)
    (h_gas : maxFlashLoanGasWarm ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + maxFlashLoanGasWarm = pre.gasLeft ∧
      Devm.output post =
        (Nat.toB256 maxFlashMinted -
          Devm.getStorVal pre sevm.currentTarget flashMintedSlot).toBytes := by
  rw [maxFlashLoanSel_eq] at h_sel
  rw [maxFlashLoanGasWarm_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0x613255ab : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_token_eq :
              B256.eqCheck sevm.currentTarget.toB256
                (Sevm.dataWord sevm 4) = 1 := by
            simp [B256.eqCheck, h_token]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0x613255ab = 1 := by decide
          have h_fork1 :
              B256.gtCheck (0x313ce567 : B256) 0x613255ab = 0 := by decide
          have h_fork2 :
              B256.gtCheck (0x5ddb7d7e : B256) 0x613255ab = 0 := by decide
          have h_fork3 :
              B256.gtCheck (0x70a08231 : B256) 0x613255ab = 1 := by decide
          have h_fork4 :
              B256.gtCheck (0x613255ab : B256) 0x613255ab = 0 := by decide
          have h_leaf :
              B256.eqCheck (0x613255ab : B256) 0x613255ab = 1 := by decide
          rw [weth10Main_eq_maxFlashLoan]
          func_run [0, (0x613255ab : B256), 1, 0, 0, 1, 0, 1, 1, 1,
            flashMintedSlot,
            Nat.toB256 maxFlashMinted -
              Devm.getStorVal pre sevm.currentTarget flashMintedSlot,
            3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 330) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst
                (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [gasLeft_withOutput, gasLeft_memRead_snd,
    Devm.gasLeft_setMach, maxFlashLoanGasWarm_eq]
  omega

/-- A non-self-token `maxFlashLoan` call returns zero without reading storage. -/
theorem maxFlashLoan_other_runCompiled (dp : DeployParams)
    {sevm : Sevm} {pre : Devm}
    (h_data : sevm.data.length.toB256 ≠ 0)
    (h_value : sevm.value = 0)
    (h_token : Sevm.dataWord sevm 4 ≠ sevm.currentTarget.toB256)
    (h_sel : Sevm.selector sevm = maxFlashLoanSel)
    (h_stack : pre.stack = [])
    (h_mem : pre.memory = Mem.empty)
    (h_gas : maxFlashLoanOtherGas ≤ pre.gasLeft) :
    ∃ post, Prog.RunCompiled sevm pre (weth10 dp) post ∧
      post.gasLeft + maxFlashLoanOtherGas = pre.gasLeft ∧
      Devm.output post = (0 : B256).toBytes := by
  rw [maxFlashLoanSel_eq] at h_sel
  rw [maxFlashLoanOtherGas_eq] at h_gas
  set g := pre.gasLeft with hg
  refine
    ⟨_,
      Prog.runCompiled_intro (G := g - 1)
        (mid := pre.setMach ⟨[], Mem.empty, g - 1⟩)
        (by simp only [gJumpdest]; omega)
        (by rw [h_stack, h_mem])
        (by
          have h_data_nz :
              B256.eqCheck sevm.data.length.toB256 0 = 0 := by
            simp [B256.eqCheck, h_data]
          have h_sel' :
              Sevm.dataWord sevm 0 >>> B256.toNat 224 =
                (0x613255ab : B256) := h_sel
          have h_value_zero : B256.eqCheck sevm.value 0 = 1 := by
            simp [B256.eqCheck, h_value]
          have h_token_ne :
              sevm.currentTarget.toB256 ≠ Sevm.dataWord sevm 4 :=
            Ne.symm h_token
          have h_token_not_eq :
              B256.eqCheck sevm.currentTarget.toB256
                (Sevm.dataWord sevm 4) = 0 := by
            simp [B256.eqCheck, h_token_ne]
          have h_fork0 :
              B256.gtCheck (0x7ecebe00 : B256) 0x613255ab = 1 := by decide
          have h_fork1 :
              B256.gtCheck (0x313ce567 : B256) 0x613255ab = 0 := by decide
          have h_fork2 :
              B256.gtCheck (0x5ddb7d7e : B256) 0x613255ab = 0 := by decide
          have h_fork3 :
              B256.gtCheck (0x70a08231 : B256) 0x613255ab = 1 := by decide
          have h_fork4 :
              B256.gtCheck (0x613255ab : B256) 0x613255ab = 0 := by decide
          have h_leaf :
              B256.eqCheck (0x613255ab : B256) 0x613255ab = 1 := by decide
          rw [weth10Main_eq_maxFlashLoan]
          func_run [0, (0x613255ab : B256), 1, 0, 0, 1, 0, 1, 1, 0, 3]
          · exact Devm.extCost_empty_word
          · exact Func.runCompiled_ret_word (G := g - 220) (e := 0) rfl
              (Devm.extCost_word_word Mem.size_write_word)
              (by simp only [Devm.gasLeft_setMach]; omega)
              (Devm.memRead_word_fst
                (by simp only [Devm.memory_setMach]; rfl))),
      ?_, rfl⟩
  simp only [gasLeft_withOutput, gasLeft_memRead_snd,
    Devm.gasLeft_setMach, maxFlashLoanOtherGas_eq]
  omega

end Weth10
end Blanc
