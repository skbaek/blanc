import Blanc.ProrataWethVaultOutbound
import Blanc.CompiledFixedInvariance
import Blanc.Composition.ProrataWethVaultStaging
import Blanc.LedgerConservation

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
    Blanc.ProrataWethVault.AllowanceSpent sevm owner shares pre post ∧
    (∀ account, wethAccount ≠ account → sevm.currentTarget ≠ account →
      Devm.getStor post account = Devm.getStor pre account) ∧
    post.logs = pre.logs ++
      [Blanc.ProrataWethVault.burnTransferLog sevm owner shares,
        wethTransferLog sevm.currentTarget receiver.toAdr assets,
        Blanc.ProrataWethVault.withdrawLogEntry sevm receiver owner assets
          shares]

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
    sevm.caller.toB256 ≠ 0 ∧
      ValidAdr receiver ∧
      receiver ≠ 0 ∧
      ValidAdr owner ∧
      owner ≠ 0 ∧
      shares.toNat ≤
        (Devm.getStorVal entry sevm.currentTarget owner).toNat ∧
      shares.toNat ≤
        (Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat ∧
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
    Blanc.ProrataWethVault.ownerHasShares_trace (R := Func.RunOk) sharesWf sharesReads
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
      allowanceSpent, burnStack, burnWf, burnReads, staged, burnRun⟩ :=
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
    exact Blanc.ProrataWethVault.supplySlot_not_validAdr (slotEq ▸ ownerValid)
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
  refine ⟨callerNonzero, ⟨receiverAdr, receiverAdrEq⟩, receiverNonzero,
    ownerValid, ownerNonzero, balanceEntry ▸ covered, roomFits,
    returns, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
      exact Blanc.ProrataWethVault.supplySlot_not_validAdr (slotEq ▸ slotValid)
    change (Devm.getStor post sevm.currentTarget).get slot =
      (Devm.getStor entry sevm.currentTarget).get slot
    rw [vaultAfter, burnSet, Stor.get_set_ne _ (Ne.symm slotNotSupply),
      Stor.get_set_ne _ (Ne.symm slotNotOwner)]
    have burnRow := ledger slot (Or.inl slotValid)
    change
      (Devm.getStor burnPre sevm.currentTarget).get slot =
        (Devm.getStor authPre sevm.currentTarget).get slot at burnRow
    rw [burnRow, ← congrFun preToAuth sevm.currentTarget]
  · rcases allowanceSpent with ownerRoute | ⟨notOwner, keyNotAddr,
      keyNotSupplySlot, covers, route⟩
    · exact Or.inl ownerRoute
    · set aKey := Blanc.ProrataWethVault.allowanceKey owner sevm.caller.toB256
        with aKeyDef
      have authKey : Devm.getStorVal entry sevm.currentTarget aKey =
          Devm.getStorVal authPre sevm.currentTarget aKey :=
        congrArg (fun storage : Stor => storage.get aKey)
          (congrFun preToAuth sevm.currentTarget)
      have keyNotOwner : aKey ≠ owner := by
        intro keyEq
        exact keyNotAddr (keyEq ▸ ownerValid)
      have survives : Devm.getStorVal post sevm.currentTarget aKey =
          Devm.getStorVal burnPre sevm.currentTarget aKey := by
        have step := congrArg (fun storage : Stor => storage.get aKey)
          (vaultAfter.trans burnSet)
        simp only [Stor.get_set_ne _ (Ne.symm keyNotSupplySlot),
          Stor.get_set_ne _ (Ne.symm keyNotOwner)] at step
        exact step
      refine Or.inr ⟨notOwner, keyNotAddr, keyNotSupplySlot, ?_, ?_⟩
      · rw [authKey]
        exact covers
      · rcases route with ⟨isMax, unchanged⟩ | decremented
        · exact Or.inl ⟨authKey.trans isMax,
            survives.trans (unchanged.trans authKey.symm)⟩
        · exact Or.inr (survives.trans (decremented.trans
            (congrArg (· - shares) authKey.symm)))
  · intro account wethNe targetNe
    rw [congrFun settleStorage account, childForeign account wethNe,
      ← congrFun stagingStorage account, burnForeign account targetNe,
      authForeign account targetNe, ← congrFun preToAuth account]
  · rw [settleLogged, childLogged, ← stagingLogs, burnLogged,
      ← authLogs, ← balanceLogs, ← guardLogs,
      show receiver.toAdr = receiverAdr by
        rw [← receiverAdrEq, toAdr_toB256]]
    simp [List.append_assoc]

/-- Shared outbound prefix: stage the three ABI arguments, price the quote from
the booked WETH balance, stage the exact share supply, and discharge the
stable-supply guard.  The result is the state at which each flow's own quote
arithmetic begins.

The snapshot is `quoteSnapshot_effect`, shared with the inbound flows; only the
argument staging in front of it is outbound-specific, and it stages three
arguments rather than two because the owner may not be the caller. -/
theorem outboundQuoteStaging_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {arithmetic : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : QuoteReadResources sevm)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.arg 0 +++ mstoreAt Blanc.ProrataWethVault.amountWord +++
        Blanc.arg 1 +++ mstoreAt Blanc.ProrataWethVault.receiverWord +++
        Blanc.arg 2 +++ mstoreAt Blanc.ProrataWethVault.ownerWord +++
        Blanc.ProrataWethVault.snapshotQuoteState arithmetic) (.ok post)) :
    ∃ quotePre image supply,
      supply = Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
      Mem.Wf quotePre.memory ∧
      Mem.Reads quotePre.memory image ∧
      Bytes.toB256
        (image.sliceD
          (Blanc.ProrataWethVault.amountWord * 32).toNat 32 0) =
        Sevm.argWord sevm 0 ∧
      Bytes.toB256
        (image.sliceD
          (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) =
        Sevm.argWord sevm 1 ∧
      Bytes.toB256
        (image.sliceD
          (Blanc.ProrataWethVault.ownerWord * 32).toNat 32 0) =
        Sevm.argWord sevm 2 ∧
      Bytes.toB256
        (image.sliceD
          (Blanc.ProrataWethVault.assetsWord * 32).toNat 32 0) =
        (entry.state.getStor wethAccount).get sevm.currentTarget.toB256 ∧
      Bytes.toB256
        (image.sliceD
          (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) = supply ∧
      [] <<+ quotePre.stack ∧
      Devm.getStor entry = Devm.getStor quotePre ∧
      entry.logs = quotePre.logs ∧
      quotePre.getCode wethAccount = entry.getCode wethAccount ∧
      Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot =
        Devm.getStorVal quotePre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
      Func.RunCompiledTo fs sevm quotePre arithmetic (.ok post) := by
  have entryReads : Mem.Reads entry.memory entry.memory.data.toList := by
    intro index
    simp
  obtain ⟨readPre, readStack, readWf, readReads, argState, argLogs,
      readRun⟩ :=
    Blanc.ProrataWethVault.outboundArgs_trace memoryWf entryReads stack run
  have argStorage : Devm.getStor entry = Devm.getStor readPre :=
    funext (getStor_eq_of_state_eq argState)
  have argCode : Devm.getCode entry = Devm.getCode readPre :=
    funext (getCode_eq_of_state_eq argState)
  have readConfig :
      DirectWethConfiguration sevm.currentTarget sevm readPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun argCode wethAccount]
    exact config.code
  obtain ⟨quotePre, image, supply, supplyEq, stable, quoteWf, quoteReads,
      carry, assetsAt, supplyAt, quoteStack, snapStorage, snapLogs, snapCode,
      quoteRun⟩ :=
    quoteSnapshot_effect readConfig readWf readReads resources readRun
  have entryStorage : Devm.getStor entry = Devm.getStor quotePre :=
    argStorage.trans snapStorage
  refine ⟨quotePre, image, supply, ?_, stable, quoteWf, quoteReads,
    carry (by decide +kernel) (by decide +kernel)
      (Blanc.ProrataWethVault.outboundArgImage_amount _ _ _ _),
    carry (by decide +kernel) (by decide +kernel)
      (Blanc.ProrataWethVault.outboundArgImage_receiver _ _ _ _),
    carry (by decide +kernel) (by decide +kernel)
      (Blanc.ProrataWethVault.outboundArgImage_owner _ _ _ _),
    ?_, supplyAt, quoteStack, entryStorage, argLogs.trans snapLogs, ?_, ?_,
    quoteRun⟩
  · rw [supplyEq]
    change (Devm.getStor readPre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor entry sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [argStorage]
  · rw [assetsAt]
    exact (congrArg
      (fun storage : Stor => storage.get sevm.currentTarget.toB256)
      (congrFun argStorage wethAccount)).symm
  · rw [snapCode, ← congrFun argCode wethAccount]
  · change (Devm.getStor entry sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor quotePre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [entryStorage]

/-- An outbound flow preserves ledger conservation: it is a paired burn, one
share row and the supply falling by exactly the same quoted amount.

No supply-underflow premise is owed.  The vault checks the burn against the
owner's own balance, and the invariant's bound corollary turns that into
`shares ≤ supply`, which is why the contract carries no separate supply
check. -/
theorem outboundEffect_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    {receiver owner assets shares returned : B256}
    (ownerValid : ValidAdr owner)
    (covered : shares.toNat ≤
      (Devm.getStorVal pre sevm.currentTarget owner).toNat)
    (effect :
      OutboundEffect sevm receiver owner assets shares returned pre post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨-, -, ownerRow, supplyRow, otherRows, -, -, -⟩ := effect
  obtain ⟨ownerAdr, ownerAdrEq⟩ := ownerValid
  subst ownerAdrEq
  refine conserved.burn (a := ownerAdr) (v := shares) ?_ ?_ supplyRow
  · intro b
    refine ⟨?_, ?_⟩
    · intro same
      subst same
      exact ownerRow.symm
    · intro different
      refine (otherRows b.toB256 ⟨b, rfl⟩ ?_).symm
      intro keyEq
      exact different (Adr.toB256_inj keyEq).symm
  · exact B256.le_of_toNat_le_toNat covered

/-- Storage and log equality is enough to move a whole outbound observation
back to an earlier state. -/
private theorem outboundEffect_lift {sevm : Sevm} {pre bodyPre post : Devm}
    {receiver owner assets shares returned : B256}
    (storage : Devm.getStor pre = Devm.getStor bodyPre)
    (logs : pre.logs = bodyPre.logs)
    (effect :
      OutboundEffect sevm receiver owner assets shares returned bodyPre post) :
    OutboundEffect sevm receiver owner assets shares returned pre post := by
  obtain ⟨returns, movement, ownerRow, supplyRow, otherRows, allowance,
    foreign, logged⟩ := effect
  have storVal : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal bodyPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor bodyPre sevm.currentTarget).get k
    rw [congrFun storage sevm.currentTarget]
  refine ⟨returns, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [congrFun storage wethAccount]
    exact movement
  · rw [storVal owner]
    exact ownerRow
  · rw [storVal Blanc.ProrataWethVault.supplySlot]
    exact supplyRow
  · intro key keyValid keyNotOwner
    rw [storVal key]
    exact otherRows key keyValid keyNotOwner
  · rcases allowance with ownerRoute | ⟨notOwner, keyNotAddr, keyNotSupplySlot,
      covers, route⟩
    · exact Or.inl ownerRoute
    · refine Or.inr ⟨notOwner, keyNotAddr, keyNotSupplySlot, ?_, ?_⟩
      · rw [storVal (Blanc.ProrataWethVault.allowanceKey owner
          sevm.caller.toB256)]
        exact covers
      · rcases route with ⟨isMax, unchanged⟩ | decremented
        · exact Or.inl ⟨(storVal _).trans isMax,
            unchanged.trans (storVal _).symm⟩
        · exact Or.inr (decremented.trans
            (congrArg (· - shares) (storVal _).symm))
  · intro account wethNe targetNe
    rw [foreign account wethNe targetNe, ← congrFun storage account]
  · rw [logged, ← logs]

/-- Join one outbound flow's quote arithmetic to the shared continuation. -/
theorem outboundBody_effect
    {fs : List Func} {sevm : Sevm}
    {entry quotePre afterPre post : Devm} {image afterImage : Bytes}
    {sharesSel assetsSel returnedSel : B256} {burnSlot : Nat}
    {receiver owner quote shares assets returned : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (entryStorage : Devm.getStor entry = Devm.getStor quotePre)
    (entryLogs : entry.logs = quotePre.logs)
    (entryCode : quotePre.getCode wethAccount = entry.getCode wethAccount)
    (supplyProjection :
      Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot =
        Devm.getStorVal quotePre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot)
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
    (afterMemImage : MemImage afterPre afterImage)
    (afterFrame : Bytes.WordFrameFrom image afterImage
      Blanc.ProrataWethVault.arithmeticScratchEnd)
    (quoteFrame : Devm.QuietFrame quotePre afterPre)
    (afterStack : quote :: [] <<+ afterPre.stack)
    (sharesAt : Bytes.toB256
      ((Bytes.writeAt afterImage
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (sharesSel * 32).toNat 32 0) = shares)
    (assetsAt : Bytes.toB256
      ((Bytes.writeAt afterImage
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (assetsSel * 32).toNat 32 0) = assets)
    (returnedAt : Bytes.toB256
      ((Bytes.writeAt afterImage
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
    (resources : OutboundChildResources sevm assetsSel)
    (lookup : fs[burnSlot]? =
      some (Blanc.ProrataWethVault.finishOutbound
        (Blanc.ProrataWethVault.loadWord sharesSel)
        (Blanc.ProrataWethVault.loadWord assetsSel)
        (Blanc.ProrataWethVault.loadWord returnedSel)))
    (afterRun : Func.RunCompiledTo fs sevm afterPre
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
    sevm.caller.toB256 ≠ 0 ∧
      ValidAdr receiver ∧
      receiver ≠ 0 ∧
      ValidAdr owner ∧
      owner ≠ 0 ∧
      shares.toNat ≤
        (Devm.getStorVal entry sevm.currentTarget owner).toNat ∧
      shares.toNat ≤
        (Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot).toNat ∧
      OutboundEffect sevm receiver owner assets shares returned entry post := by
  have quoteStorage : Devm.getStor quotePre = Devm.getStor afterPre :=
    funext (getStor_eq_of_state_eq quoteFrame.1)
  have afterConfig :
      DirectWethConfiguration sevm.currentTarget sevm afterPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← getCode_eq_of_state_eq quoteFrame.1 wethAccount, entryCode]
    exact config.code
  have carry : ∀ {offset : Nat} {w : B256},
      Blanc.ProrataWethVault.arithmeticScratchEnd ≤ offset →
      Bytes.toB256 (image.sliceD offset 32 0) = w →
      Bytes.toB256 (afterImage.sliceD offset 32 0) = w := by
    intro offset w above value
    rw [afterFrame offset above]
    exact value
  have supplyBridge :
      Devm.getStorVal entry sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot =
        Devm.getStorVal afterPre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot := by
    rw [supplyProjection]
    change (Devm.getStor quotePre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor afterPre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [quoteStorage]
  have storVal : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal afterPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor entry sevm.currentTarget).get k =
      (Devm.getStor afterPre sevm.currentTarget).get k
    rw [congrFun entryStorage sevm.currentTarget,
      congrFun quoteStorage sevm.currentTarget]
  obtain ⟨callerNonzero, receiverValid, receiverNonzero, ownerValid,
      ownerNonzero, covered, roomFits, effect⟩ :=
    outboundAfterQuote_effect afterConfig afterMemImage.1 afterMemImage.2
      (carry (by decide +kernel) receiverAt)
      (carry (by decide +kernel) ownerAt)
      (by
        rw [← supplyBridge]
        exact carry (by decide +kernel) supplyAt)
      sharesAt assetsAt returnedAt sharesAbove sharesBelow assetsAbove
      assetsBelow returnedAbove returnedBelow afterStack resources lookup
      afterRun
  exact ⟨callerNonzero, receiverValid, receiverNonzero, ownerValid,
    ownerNonzero, (storVal owner) ▸ covered,
    (storVal Blanc.ProrataWethVault.supplySlot) ▸ roomFits,
    outboundEffect_lift (entryStorage.trans quoteStorage)
      (entryLogs.trans quoteFrame.2) effect⟩

/-- Exact compiled body effect of `withdraw(assets, receiver, owner)`. -/
theorem withdraw_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (readResources : QuoteReadResources sevm)
    (childResources : OutboundChildResources sevm
      Blanc.ProrataWethVault.amountWord)
    (afterLookup : fs[Blanc.ProrataWethVault.withdrawAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.withdrawAfterQuote)
    (burnLookup : fs[Blanc.ProrataWethVault.withdrawBurnSlot]? =
      some Blanc.ProrataWethVault.withdrawBurn)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry Blanc.ProrataWethVault.withdraw
      (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.previewWithdrawN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      Sevm.argWord sevm 1 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 2) ∧
      Sevm.argWord sevm 2 ≠ 0 ∧
      (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤
        (Devm.getStorVal entry sevm.currentTarget
          (Sevm.argWord sevm 2)).toNat ∧
      (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤
        supply.toNat ∧
      OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        (Sevm.argWord sevm 0)
        (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        entry post := by
  rw [Blanc.ProrataWethVault.withdraw_shape] at run
  obtain ⟨quotePre, image, supply, supplyEq, stable, quoteWf, quoteReads,
      amountAt, receiverAt, ownerAt, assetsAt, supplyAt, quoteStack,
      quoteStorage, quoteLogs, quoteCode, supplyProjection, quoteRun⟩ :=
    outboundQuoteStaging_effect config memoryWf readResources stack run
  obtain ⟨quoteFits, afterPre, afterImage, afterStack, afterMemImage,
      afterFrame, quoteFrame, afterRun⟩ :=
    Blanc.ProrataWethVault.withdrawQuote_arithmetic_trace quoteWf quoteReads
      amountAt assetsAt supplyAt stable quoteStack afterLookup quoteRun
  rw [Blanc.ProrataWethVault.withdrawAfterQuote_shape] at afterRun
  rw [Blanc.ProrataWethVault.withdrawBurn_shape] at burnLookup
  have amountAtAfter : Bytes.toB256
      (afterImage.sliceD
        (Blanc.ProrataWethVault.amountWord * 32).toNat 32 0) =
        Sevm.argWord sevm 0 := by
    rw [afterFrame _ (by decide +kernel)]
    exact amountAt
  have supplyAtEntry : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
      Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot := by
    rw [supplyAt, supplyEq]
  obtain ⟨callerNonzero, receiverValid, receiverNonzero, ownerValid,
      ownerNonzero, covered, roomFits, effect⟩ :=
    outboundBody_effect config quoteStorage quoteLogs quoteCode
      supplyProjection receiverAt ownerAt supplyAtEntry afterMemImage
      afterFrame quoteFrame afterStack
      (sharesSel := Blanc.ProrataWethVault.quoteWord)
      (assetsSel := Blanc.ProrataWethVault.amountWord)
      (returnedSel := Blanc.ProrataWethVault.quoteWord)
      (quote := (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat)))
      (shares := (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat)))
      (assets := Sevm.argWord sevm 0)
      (returned := (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat)))
      (toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _))
      (by
        rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _
          (Or.inl (by decide +kernel))]
        exact amountAtAfter)
      (toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      childResources burnLookup afterRun
  refine ⟨supply, supplyEq, stable, quoteFits, callerNonzero, receiverValid,
    receiverNonzero, ownerValid, ownerNonzero, covered, ?_, effect⟩
  have supplyNat : supply.toNat =
      (Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat :=
    congrArg B256.toNat supplyEq
  omega

/-- Exact compiled body effect of `redeem(shares, receiver, owner)`. -/
theorem redeem_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (readResources : QuoteReadResources sevm)
    (childResources : OutboundChildResources sevm
      Blanc.ProrataWethVault.quoteWord)
    (afterLookup : fs[Blanc.ProrataWethVault.redeemAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.redeemAfterQuote)
    (burnLookup : fs[Blanc.ProrataWethVault.redeemBurnSlot]? =
      some Blanc.ProrataWethVault.redeemBurn)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry Blanc.ProrataWethVault.redeem
      (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.previewRedeemN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      Sevm.argWord sevm 1 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 2) ∧
      Sevm.argWord sevm 2 ≠ 0 ∧
      (Sevm.argWord sevm 0).toNat ≤
        (Devm.getStorVal entry sevm.currentTarget
          (Sevm.argWord sevm 2)).toNat ∧
      (Sevm.argWord sevm 0).toNat ≤ supply.toNat ∧
      OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
        (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        (Sevm.argWord sevm 0)
        (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        entry post := by
  rw [Blanc.ProrataWethVault.redeem_shape] at run
  obtain ⟨quotePre, image, supply, supplyEq, stable, quoteWf, quoteReads,
      amountAt, receiverAt, ownerAt, assetsAt, supplyAt, quoteStack,
      quoteStorage, quoteLogs, quoteCode, supplyProjection, quoteRun⟩ :=
    outboundQuoteStaging_effect config memoryWf readResources stack run
  obtain ⟨quoteFits, afterPre, afterImage, afterStack, afterMemImage,
      afterFrame, quoteFrame, afterRun⟩ :=
    Blanc.ProrataWethVault.redeemQuote_arithmetic_trace quoteWf quoteReads
      amountAt assetsAt supplyAt stable quoteStack afterLookup quoteRun
  rw [Blanc.ProrataWethVault.redeemAfterQuote_shape] at afterRun
  rw [Blanc.ProrataWethVault.redeemBurn_shape] at burnLookup
  have amountAtAfter : Bytes.toB256
      (afterImage.sliceD
        (Blanc.ProrataWethVault.amountWord * 32).toNat 32 0) =
        Sevm.argWord sevm 0 := by
    rw [afterFrame _ (by decide +kernel)]
    exact amountAt
  have supplyAtEntry : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
      Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot := by
    rw [supplyAt, supplyEq]
  obtain ⟨callerNonzero, receiverValid, receiverNonzero, ownerValid,
      ownerNonzero, covered, roomFits, effect⟩ :=
    outboundBody_effect config quoteStorage quoteLogs quoteCode
      supplyProjection receiverAt ownerAt supplyAtEntry afterMemImage
      afterFrame quoteFrame afterStack
      (sharesSel := Blanc.ProrataWethVault.amountWord)
      (assetsSel := Blanc.ProrataWethVault.quoteWord)
      (returnedSel := Blanc.ProrataWethVault.quoteWord)
      (shares := Sevm.argWord sevm 0)
      (assets := (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat)))
      (returned := (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat)))
      (by
        rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _
          (Or.inl (by decide +kernel))]
        exact amountAtAfter)
      (toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _))
      (toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      childResources burnLookup afterRun
  refine ⟨supply, supplyEq, stable, quoteFits, callerNonzero, receiverValid,
    receiverNonzero, ownerValid, ownerNonzero, covered, ?_, effect⟩
  have supplyNat : supply.toNat =
      (Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat :=
    congrArg B256.toNat supplyEq
  omega

private theorem withdrawAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.withdrawAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.withdrawAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.withdrawAfterQuoteSlot]

private theorem redeemAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.redeemAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.redeemAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.redeemAfterQuoteSlot]

private theorem withdrawBurn_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.withdrawBurnSlot]? =
      some Blanc.ProrataWethVault.withdrawBurn := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.withdrawBurnSlot]

private theorem redeemBurn_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.redeemBurnSlot]? =
      some Blanc.ProrataWethVault.redeemBurn := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.redeemBurnSlot]

private theorem withdraw_mem_vaultFuncs :
    (selector "withdraw" [.uint256, .address, .address],
      Blanc.ProrataWethVault.routed 3 Blanc.ProrataWethVault.withdraw) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

private theorem redeem_mem_vaultFuncs :
    (selector "redeem" [.uint256, .address, .address],
      Blanc.ProrataWethVault.routed 3 Blanc.ProrataWethVault.redeem) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

/-- Resources for a compiled outbound endpoint, tied to the exact selector's
body rather than asserted for every state. -/
def OutboundCompiledResources (sevm : Sevm) (assetsSel : B256) : Prop :=
  QuoteReadResources sevm ∧ OutboundChildResources sevm assetsSel

/-- Public compiled `withdraw(amount, receiver, owner)`.

The vault burns exactly `ceil(assets * D / X)` shares from the owner, pays the
receiver exactly `assets` WETH through the exact configured `transfer` child,
decreases the supply, emits the burn `Transfer` then the child's `Transfer`
then `Withdraw`, and returns the burnt shares.  The rounding is *up*, against
the redeemer and in the vault's favour.  No other share row and no other
account's storage moves. -/
theorem withdraw_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : OutboundCompiledResources sevm
      Blanc.ProrataWethVault.amountWord)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "withdraw" [.uint256, .address, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.previewWithdrawN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 2) ∧
        Sevm.argWord sevm 2 ≠ 0 ∧
        (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 2)).toNat ∧
        (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤ supply.toNat ∧
        OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
          (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          (Nat.toB256 (Blanc.ProrataWethVault.previewWithdrawN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          pre post := by
  rcases Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs
      run selectorEq withdraw_mem_vaultFuncs with
    ⟨bodyPre, valueZero, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyConfig :
      DirectWethConfiguration sevm.currentTarget sevm bodyPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← getCode_eq_of_state_eq entryState wethAccount]
    exact config.code
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  obtain ⟨supply, supplyEq, stable, quoteFits, callerNonzero, receiverValid,
      receiverNonzero, ownerValid, ownerNonzero, covered, roomFits, effect⟩ :=
    withdraw_body_effect bodyConfig bodyWf resources.1 resources.2
      withdrawAfterQuote_lookup withdrawBurn_lookup nil_pref bodyRun
  have storEq : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have storValEq : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal bodyPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor bodyPre sevm.currentTarget).get k
    rw [congrFun storEq sevm.currentTarget]
  have wethEq :
      (pre.state.getStor wethAccount).get sevm.currentTarget.toB256 =
        (bodyPre.state.getStor wethAccount).get
          sevm.currentTarget.toB256 := by
    rw [entryState]
  refine ⟨valueZero, supply, ?_, stable, ?_, callerNonzero, receiverValid,
    receiverNonzero, ownerValid, ownerNonzero, ?_, ?_, ?_⟩
  · rw [supplyEq, storValEq Blanc.ProrataWethVault.supplySlot]
  · rw [wethEq]
    exact quoteFits
  · rw [storValEq (Sevm.argWord sevm 2), wethEq]
    exact covered
  · rw [wethEq]
    exact roomFits
  · rw [wethEq]
    exact outboundEffect_lift storEq entryLogs effect

/-- Public compiled `redeem(amount, receiver, owner)`.

The vault burns exactly `shares` from the owner, pays the receiver exactly
`floor(shares * X / D)` WETH through the exact configured `transfer` child,
decreases the supply, emits the burn `Transfer` then the child's `Transfer`
then `Withdraw`, and returns the assets paid.  The rounding is *down*, against
the redeemer and in the vault's favour.  No other share row and no other
account's storage moves. -/
theorem redeem_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : OutboundCompiledResources sevm
      Blanc.ProrataWethVault.quoteWord)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq : Sevm.selector sevm =
      selector "redeem" [.uint256, .address, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.previewRedeemN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 2) ∧
        Sevm.argWord sevm 2 ≠ 0 ∧
        (Sevm.argWord sevm 0).toNat ≤
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 2)).toNat ∧
        (Sevm.argWord sevm 0).toNat ≤ supply.toNat ∧
        OutboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)
          (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.previewRedeemN
          (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
          pre post := by
  rcases Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs
      run selectorEq redeem_mem_vaultFuncs with
    ⟨bodyPre, valueZero, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyConfig :
      DirectWethConfiguration sevm.currentTarget sevm bodyPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← getCode_eq_of_state_eq entryState wethAccount]
    exact config.code
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  obtain ⟨supply, supplyEq, stable, quoteFits, callerNonzero, receiverValid,
      receiverNonzero, ownerValid, ownerNonzero, covered, roomFits, effect⟩ :=
    redeem_body_effect bodyConfig bodyWf resources.1 resources.2
      redeemAfterQuote_lookup redeemBurn_lookup nil_pref bodyRun
  have storEq : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have storValEq : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal bodyPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor bodyPre sevm.currentTarget).get k
    rw [congrFun storEq sevm.currentTarget]
  have wethEq :
      (pre.state.getStor wethAccount).get sevm.currentTarget.toB256 =
        (bodyPre.state.getStor wethAccount).get
          sevm.currentTarget.toB256 := by
    rw [entryState]
  refine ⟨valueZero, supply, ?_, stable, ?_, callerNonzero, receiverValid,
    receiverNonzero, ownerValid, ownerNonzero, ?_, ?_, ?_⟩
  · rw [supplyEq, storValEq Blanc.ProrataWethVault.supplySlot]
  · rw [wethEq]
    exact quoteFits
  · rw [storValEq (Sevm.argWord sevm 2)]
    exact covered
  · exact roomFits
  · rw [wethEq]
    exact outboundEffect_lift storEq entryLogs effect

end Blanc.Composition.ProrataWethVault
