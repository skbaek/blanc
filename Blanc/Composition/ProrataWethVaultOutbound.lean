import Blanc.ProrataWethVaultOutbound
import Blanc.CompiledFixedInvariance
import Blanc.Composition.ProrataWethVaultStaging

/-!
# WETH-backed compiled outbound flows

The contract-family module owns the vault-local half of `withdraw` and
`redeem`: argument staging, the exact quotes, the caller/receiver/owner
guards, the owner share-balance check, the allowance path, the burn, and the
post-child settlement.  This composition owner joins that half to the two exact
configured WETH children the flows actually execute — the `balanceOf(vault)`
read that prices the quote and the `transfer(receiver, assets)` that pays the
redemption out — and lifts the result through the compiled vault selectors.

The outbound direction is not the inbound one reversed.  Its share write
happens *before* the WETH crossing, so the vault's own ledger has to survive
the child rather than be established after it; that is what
`callWethTransfer_worldEffect` supplies.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

/-- Resources required by the exact WETH `transfer` child of one outbound flow.
As with the inbound transfer, the gas obligation is tied to the fixed staging
line that produces the call state, not asserted universally. -/
def OutboundChildResources (sevm : Sevm) (assetsSel : B256) : Prop :=
  sevm.depth ≠ 0 ∧
    sevm.isStatic = false ∧
    ∀ stagingEntry callPre,
      Line.Run sevm stagingEntry
        (transferStaging Blanc.ProrataWethVault.receiverWord assetsSel)
        callPre →
      CallGasAvailable callPre 68

/-- Exact observation made by a successful compiled outbound flow.

The WETH row moves by the exact quoted asset amount from the vault to the
receiver; the owner's share row and the share supply each fall by the exact
quoted share amount; no *other* share row moves; no third account's storage
moves; the vault's burn `Transfer` precedes the child's `Transfer` and the
ERC-4626 `Withdraw`; and the returned word is the quoted value.

Share rows are constrained pointwise rather than by one whole-`Stor` equation
because the allowance route also decrements one allowance slot, and that slot
is not address-shaped.  Quantifying only over address-shaped keys says exactly
what the vault guarantees without asserting the allowance slot did not move. -/
def OutboundEffect
    (sevm : Sevm) (receiver owner assets shares returned : B256)
    (pre post : Devm) : Prop :=
  ReturnsWord returned post ∧
    Transfer (Stor.rest (Devm.getStor pre wethAccount)) sevm.currentTarget
      assets receiver.toAdr (Stor.rest (Devm.getStor post wethAccount)) ∧
    Devm.getStorVal post sevm.currentTarget owner =
      Devm.getStorVal pre sevm.currentTarget owner - shares ∧
    Devm.getStorVal post sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot =
      Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot - shares ∧
    (∀ key, ValidAdr key → key ≠ owner →
      Devm.getStorVal post sevm.currentTarget key =
        Devm.getStorVal pre sevm.currentTarget key) ∧
    (∀ account, wethAccount ≠ account → sevm.currentTarget ≠ account →
      Devm.getStor post account = Devm.getStor pre account) ∧
    post.logs = pre.logs ++
      [Blanc.ProrataWethVault.burnTransferLog sevm owner shares,
        wethTransferLog sevm.currentTarget receiver.toAdr assets,
        Blanc.ProrataWethVault.withdrawLogEntry sevm receiver owner assets
          shares]

/-- The reserved supply word is not address-shaped, so it can never collide
with an owner's share row. -/
theorem supplySlot_not_validAdr :
    ¬ ValidAdr Blanc.ProrataWethVault.supplySlot := by
  rw [validAdr_iff]
  decide +kernel

/-- Exact effect of an outbound flow from its auxiliary continuation onward.

The three word parameters are the operation words each flow settles with:
`withdraw` supplies `(quote, amount, quote)` and `redeem` supplies
`(amount, quote, quote)`.  Everything after the quote is shared, including the
allowance path and the exact WETH `transfer` child, so both flows reach this
one theorem. -/
theorem outboundAfterQuote_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {image : Bytes}
    {sharesSel assetsSel returnedSel : B256} {burnSlot : Nat}
    {receiver owner quote shares assets returned : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (memoryReads : Mem.Reads entry.memory image)
    (receiverAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) =
        receiver)
    (ownerAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.ownerWord * 32).toNat 32 0) =
        owner)
    (supplyAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
        Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot)
    (sharesAt : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (sharesSel * 32).toNat 32 0) = shares)
    (assetsAt : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (assetsSel * 32).toNat 32 0) = assets)
    (returnedAt : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (returnedSel * 32).toNat 32 0) = returned)
    (sharesAbove : 1024 ≤ (sharesSel * 32).toNat)
    (sharesBelow : (sharesSel * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (assetsAbove : 1024 ≤ (assetsSel * 32).toNat)
    (assetsBelow : (assetsSel * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (returnedAbove : 1024 ≤ (returnedSel * 32).toNat)
    (returnedBelow : (returnedSel * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (stack : quote :: [] <<+ entry.stack)
    (resources : OutboundChildResources sevm assetsSel)
    (lookup : fs[burnSlot]? =
      some (Blanc.ProrataWethVault.finishOutbound
        (Blanc.ProrataWethVault.loadWord sharesSel)
        (Blanc.ProrataWethVault.loadWord assetsSel)
        (Blanc.ProrataWethVault.loadWord returnedSel)))
    (run : Func.RunCompiledTo fs sevm entry
      (mstoreAt Blanc.ProrataWethVault.quoteWord +++
        Blanc.ProrataWethVault.nonzeroCaller
          (Blanc.ProrataWethVault.nonzeroStagedAddress
            Blanc.ProrataWethVault.receiverWord
            (Blanc.ProrataWethVault.nonzeroStagedAddress
              Blanc.ProrataWethVault.ownerWord
              (Blanc.ProrataWethVault.ownerHasShares
                (Blanc.ProrataWethVault.loadWord sharesSel)
                (Blanc.ProrataWethVault.loadWord
                    Blanc.ProrataWethVault.ownerWord +++
                  caller ::: eq :::
                  (.call burnSlot <?>
                    Blanc.ProrataWethVault.spendAllowance
                      (Blanc.ProrataWethVault.loadWord
                        Blanc.ProrataWethVault.ownerWord)
                      [caller]
                      (Blanc.ProrataWethVault.loadWord sharesSel)
                      burnSlot)))))) (.ok post)) :
    OutboundEffect sevm receiver owner assets shares returned entry post := by
  obtain ⟨depth, dynamic, gasAvailable⟩ := resources

  -- Caller, receiver and owner guards.
  obtain ⟨sharesPre, callerNonzero, receiverValid, receiverNonzero,
      ownerValid, ownerNonzero, sharesStack, sharesWf, sharesReads,
      guardState, guardLogs, sharesRun⟩ :=
    Blanc.ProrataWethVault.outboundGuards_trace memoryWf memoryReads
      receiverAt ownerAt stack run
  have guardStorage : Devm.getStor entry = Devm.getStor sharesPre :=
    funext (getStor_eq_of_state_eq guardState)
  have guardCode : Devm.getCode entry = Devm.getCode sharesPre :=
    funext (getCode_eq_of_state_eq guardState)
  set quoteImage := Bytes.writeAt image
    (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes
    with quoteImageDef
  have receiverAtQuote : Bytes.toB256
      (quoteImage.sliceD
        (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) = receiver := by
    rw [quoteImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAt
    · left
      decide +kernel
  have ownerAtQuote : Bytes.toB256
      (quoteImage.sliceD
        (Blanc.ProrataWethVault.ownerWord * 32).toNat 32 0) = owner := by
    rw [quoteImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAt
    · left
      decide +kernel
  have supplyAtQuote : Bytes.toB256
      (quoteImage.sliceD
        (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
      Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot := by
    rw [quoteImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact supplyAt
    · right
      decide +kernel

  -- Owner share-balance guard.
  obtain ⟨authPre, balance, balanceEq, covered, authStack, authWf, authReads,
      balanceStorage, balanceCode, balanceLogs, authRun⟩ :=
    Blanc.ProrataWethVault.ownerHasShares_trace sharesWf sharesReads
      ownerAtQuote sharesAt sharesBelow sharesStack sharesRun
  set balanceImage := Bytes.writeAt quoteImage
    (Blanc.ProrataWethVault.balanceWord * 32).toNat balance.toBytes
    with balanceImageDef
  change Mem.Reads authPre.memory balanceImage at authReads

  -- Authorization: owner is caller, or a staged allowance covers the burn.
  have scratchOffset :
      (Blanc.ProrataWethVault.scratchWord * 32).toNat = 800 := by
    decide +kernel
  have allowanceOffset :
      (Blanc.ProrataWethVault.allowanceWord * 32).toNat = 1248 := by
    decide +kernel
  have balanceOffset :
      (Blanc.ProrataWethVault.balanceWord * 32).toNat = 1216 := by
    decide +kernel
  have ownerAtBalance : Bytes.toB256
      (balanceImage.sliceD
        (Blanc.ProrataWethVault.ownerWord * 32).toNat 32 0) = owner := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAtQuote
    · left
      decide +kernel
  have sharesAtBalance : Bytes.toB256
      (balanceImage.sliceD (sharesSel * 32).toNat 32 0) = shares := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact sharesAt
    · left
      exact sharesBelow
  obtain ⟨burnPre, burnImage, ledger, authForeign, authLogs, authCode,
      burnStack, burnWf, burnReads, staged, burnRun⟩ :=
    Blanc.ProrataWethVault.outboundAuthorization_trace authWf authReads
      ownerAtBalance sharesAtBalance (by omega) (by omega) (by omega)
      authStack lookup authRun

  -- Carry every operation word through whichever authorization route ran.
  have carryStaged : ∀ {w v : B256}, 64 ≤ (w * 32).toNat →
      (Blanc.ProrataWethVault.scratchWord * 32).toNat + 32 ≤ (w * 32).toNat →
      (w * 32).toNat + 32 ≤
        (Blanc.ProrataWethVault.allowanceWord * 32).toNat →
      Bytes.toB256 (balanceImage.sliceD (w * 32).toNat 32 0) = v →
      Bytes.toB256 (burnImage.sliceD (w * 32).toNat 32 0) = v := by
    intro w v above scratch allowance value
    exact (Blanc.ProrataWethVault.outboundStagedImage_readWord staged above
      scratch allowance).trans value
  have balanceAtBalance : Bytes.toB256
      (balanceImage.sliceD
        (Blanc.ProrataWethVault.balanceWord * 32).toNat 32 0) = balance := by
    rw [balanceImageDef]
    exact Bytes.readWord_writeAt_self _ _ _
  have assetsAtBalance : Bytes.toB256
      (balanceImage.sliceD (assetsSel * 32).toNat 32 0) = assets := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact assetsAt
    · left
      exact assetsBelow
  have returnedAtBalance : Bytes.toB256
      (balanceImage.sliceD (returnedSel * 32).toNat 32 0) = returned := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact returnedAt
    · left
      exact returnedBelow
  have receiverAtBalance : Bytes.toB256
      (balanceImage.sliceD
        (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) = receiver := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAtQuote
    · left
      decide +kernel
  have supplyAtBalance : Bytes.toB256
      (balanceImage.sliceD
        (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
      Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact supplyAtQuote
    · left
      decide +kernel

  -- Burn the shares and decrease the supply.
  rw [Blanc.ProrataWethVault.finishOutbound_shape] at burnRun
  obtain ⟨childEntry, roomFits, burnSet, burnForeign, burnLogged, burnCode,
      childStack, childWf, childReads, childRun⟩ :=
    Blanc.ProrataWethVault.outboundBurn_trace burnWf burnReads
      (carryStaged (by omega) (by omega) (by omega) sharesAtBalance)
      (carryStaged (by decide +kernel) (by decide +kernel) (by decide +kernel)
        ownerAtBalance)
      (carryStaged (by decide +kernel) (by decide +kernel) (by decide +kernel)
        balanceAtBalance)
      (carryStaged (by decide +kernel) (by decide +kernel) (by decide +kernel)
        supplyAtBalance)
      burnStack burnRun
  set childImage := Bytes.writeAt burnImage 0 shares.toBytes
    with childImageDef
  change Mem.Reads childEntry.memory childImage at childReads

  -- Cross the exact configured WETH `transfer` child.
  obtain ⟨receiverAdr, receiverAdrEq⟩ := receiverValid
  obtain ⟨callPre, callPost, staging, crossing, suffix⟩ :=
    callWethTransfer_trace childRun
  have receiverAtChild : Bytes.toB256
      (childImage.sliceD
        (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) =
      receiverAdr.toB256 := by
    rw [childImageDef, Bytes.readWord_writeAt_of_disjoint, receiverAdrEq]
    · exact carryStaged (by decide +kernel) (by decide +kernel)
        (by decide +kernel) receiverAtBalance
    · right
      decide +kernel
  have assetsAtChild : Bytes.toB256
      (childImage.sliceD (assetsSel * 32).toNat 32 0) = assets := by
    rw [childImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact carryStaged (by omega) (by omega) (by omega) assetsAtBalance
    · right
      omega
  have stagingCode : Devm.getCode childEntry = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold transferStaging Blanc.ProrataWethVault.loadWord mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun (guardCode.trans (balanceCode.trans (authCode.trans
      (burnCode.trans stagingCode)))) wethAccount]
    exact config.code
  obtain ⟨tailPre, movement, childForeign, childLogged, -, tailWf,
      tailWindow, tailRun⟩ :=
    callWethTransfer_worldEffect callConfig ⟨childWf, childReads⟩
      (sliceBytes_of_toB256 receiverAtChild)
      (sliceBytes_of_toB256 assetsAtChild)
      (by decide +kernel) (by omega) staging depth dynamic
      (gasAvailable childEntry callPre staging) crossing suffix

  -- Transport every operation word across the calldata frame and the child.
  have tailReads : Mem.Reads tailPre.memory tailPre.memory.data.toList := by
    intro index
    simp
  have carry : ∀ {offset : Nat} {w : B256}, 96 ≤ offset →
      Bytes.toB256 (childImage.sliceD offset 32 0) = w →
      Bytes.toB256 (tailPre.memory.data.toList.sliceD offset 32 0) = w := by
    intro offset w above value
    have childWindow : MemWordAt childEntry offset w :=
      MemWordAt.of_memImage ⟨childWf, childReads⟩ (sliceBytes_of_toB256 value)
    exact toB256_of_sliceBytes
      ((tailWindow above childWindow).slice_eq tailReads)
  have carryChild : ∀ {w v : B256}, 96 ≤ (w * 32).toNat →
      64 ≤ (w * 32).toNat →
      (Blanc.ProrataWethVault.scratchWord * 32).toNat + 32 ≤ (w * 32).toNat →
      (w * 32).toNat + 32 ≤
        (Blanc.ProrataWethVault.allowanceWord * 32).toNat →
      Bytes.toB256 (balanceImage.sliceD (w * 32).toNat 32 0) = v →
      Bytes.toB256
        (tailPre.memory.data.toList.sliceD (w * 32).toNat 32 0) = v := by
    intro w v above64 above scratch allowance value
    refine carry above64 ?_
    rw [childImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact carryStaged above scratch allowance value
    · right
      omega

  -- Settle: the exact `Withdraw` entry and the returned word.
  obtain ⟨returns, settleStorage, settleLogged⟩ :=
    Blanc.ProrataWethVault.outboundSettle_trace tailWf tailReads
      (carryChild (by omega) (by omega) (by omega) (by omega) assetsAtBalance)
      (carryChild (by omega) (by omega) (by omega) (by omega) sharesAtBalance)
      (carryChild (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) ownerAtBalance)
      (carryChild (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (by decide +kernel) receiverAtBalance)
      (carryChild (by omega) (by omega) (by omega) (by omega)
        returnedAtBalance)
      (by omega) (by omega) nil_pref tailRun

  -- Assemble the exact outbound observation.
  have stagingStorage : Devm.getStor childEntry = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by
      unfold transferStaging Blanc.ProrataWethVault.loadWord mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have stagingLogs : childEntry.logs = callPre.logs :=
    Line.of_inv Devm.logs (by
      unfold transferStaging Blanc.ProrataWethVault.loadWord mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have ownerNotSupply : owner ≠ Blanc.ProrataWethVault.supplySlot := by
    intro slotEq
    exact supplySlot_not_validAdr (slotEq ▸ ownerValid)
  have preToAuth : Devm.getStor entry = Devm.getStor authPre :=
    guardStorage.trans balanceStorage
  have vaultAfter : Devm.getStor post sevm.currentTarget =
      Devm.getStor childEntry sevm.currentTarget := by
    rw [congrFun settleStorage sevm.currentTarget,
      childForeign sevm.currentTarget config.distinct,
      ← congrFun stagingStorage sevm.currentTarget]
  have balanceEntry :
      balance = Devm.getStorVal entry sevm.currentTarget owner := by
    rw [balanceEq]
    change
      (Devm.getStor sharesPre sevm.currentTarget).get owner =
        (Devm.getStor entry sevm.currentTarget).get owner
    rw [← congrFun guardStorage sevm.currentTarget]
  refine ⟨returns, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have wethAfter : Devm.getStor post wethAccount =
        Devm.getStor tailPre wethAccount :=
      congrFun settleStorage wethAccount
    have wethBefore : Devm.getStor entry wethAccount =
        Devm.getStor callPre wethAccount := by
      rw [preToAuth, ← authForeign wethAccount (Ne.symm config.distinct),
        ← burnForeign wethAccount (Ne.symm config.distinct),
        congrFun stagingStorage wethAccount]
    rw [wethAfter, wethBefore,
      show receiver.toAdr = receiverAdr by
        rw [← receiverAdrEq, toAdr_toB256]]
    exact movement
  · change (Devm.getStor post sevm.currentTarget).get owner = _
    rw [vaultAfter, burnSet, Stor.get_set_ne _ (Ne.symm ownerNotSupply),
      Stor.get_set_self, ← balanceEntry]
  · change (Devm.getStor post sevm.currentTarget).get
      Blanc.ProrataWethVault.supplySlot = _
    rw [vaultAfter, burnSet, Stor.get_set_self]
  · intro slot slotValid slotNotOwner
    have slotNotSupply : slot ≠ Blanc.ProrataWethVault.supplySlot := by
      intro slotEq
      exact supplySlot_not_validAdr (slotEq ▸ slotValid)
    change (Devm.getStor post sevm.currentTarget).get slot =
      (Devm.getStor entry sevm.currentTarget).get slot
    rw [vaultAfter, burnSet, Stor.get_set_ne _ (Ne.symm slotNotSupply),
      Stor.get_set_ne _ (Ne.symm slotNotOwner)]
    have burnRow := ledger slot (Or.inl slotValid)
    change
      (Devm.getStor burnPre sevm.currentTarget).get slot =
        (Devm.getStor authPre sevm.currentTarget).get slot at burnRow
    rw [burnRow, ← congrFun preToAuth sevm.currentTarget]
  · intro account wethNe targetNe
    rw [congrFun settleStorage account, childForeign account wethNe,
      ← congrFun stagingStorage account, burnForeign account targetNe,
      authForeign account targetNe, ← congrFun preToAuth account]
  · rw [settleLogged, childLogged, ← stagingLogs, burnLogged,
      ← authLogs, ← balanceLogs, ← guardLogs,
      show receiver.toAdr = receiverAdr by
        rw [← receiverAdrEq, toAdr_toB256]]
    simp [List.append_assoc]

end Blanc.Composition.ProrataWethVault
