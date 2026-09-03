import Blanc.ProrataWethVaultInbound
import Blanc.CompiledFixedInvariance
import Blanc.Composition.ProrataWethVaultStaging

/-!
# WETH-backed compiled inbound flows

The contract-family module owns the vault-local half of `deposit` and `mint`:
argument staging, the exact pre-transfer quotes, the caller/receiver and
supply-room guards, and the settlement tail.  This composition owner joins
that half to the two exact configured WETH children the flows actually
execute — the `balanceOf(vault)` read that prices the quote and the
`transferFrom(caller, vault, assets)` transfer that settles it — and lifts the
result through the compiled vault selectors.

The quote is taken from the WETH balance booked *before* the inbound transfer,
which is why the read and the transfer are separate crossings here rather than
one combined premise.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

/-- Resources required by the exact WETH `transferFrom` child of one inbound
flow.  As with the asset query, the gas obligation is tied to the fixed
staging line that produces the call state, not asserted universally. -/
def InboundChildResources (sevm : Sevm) (assetsSourceWord : B256) : Prop :=
  sevm.depth ≠ 0 ∧
    sevm.isStatic = false ∧
    ∀ stagingEntry callPre,
      Line.Run sevm stagingEntry
        (transferFromStaging assetsSourceWord) callPre →
      CallGasAvailable callPre 100

/-- Exact observation made by a successful compiled inbound flow.

The WETH row moves by the exact quoted asset amount from the caller to the
vault; the receiver's share row is credited and the share supply increased by
the exact quoted share amount; no third account's storage moves; the child's
`Transfer` precedes the vault's share `Transfer` and `Deposit`; and the
returned word is the quoted value. -/
def InboundEffect (sevm : Sevm) (receiver assets shares returned : B256)
    (pre post : Devm) : Prop :=
  ReturnsWord returned post ∧
    Transfer (Stor.rest (Devm.getStor pre wethAccount)) sevm.caller assets
      sevm.currentTarget (Stor.rest (Devm.getStor post wethAccount)) ∧
    Devm.getStor post sevm.currentTarget =
      ((Devm.getStor pre sevm.currentTarget).set receiver
          (Devm.getStorVal pre sevm.currentTarget receiver + shares)).set
        Blanc.ProrataWethVault.supplySlot
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot + shares) ∧
    (∀ account, wethAccount ≠ account → sevm.currentTarget ≠ account →
      Devm.getStor post account = Devm.getStor pre account) ∧
    post.logs = pre.logs ++
      [wethTransferLog sevm.caller sevm.currentTarget assets,
        Blanc.ProrataWethVault.mintTransferLog sevm receiver shares,
        Blanc.ProrataWethVault.depositLogEntry sevm receiver assets shares]

private theorem sliceBytes_of_toB256 {image : Bytes} {offset : Nat} {w : B256}
    (value : Bytes.toB256 (image.sliceD offset 32 0) = w) :
    image.sliceD offset 32 0 = w.toBytes := by
  rw [← value]
  exact (Bytes.toBytes_toB256_of_length (List.length_sliceD _ _ _ _)).symm

private theorem toB256_of_sliceBytes {image : Bytes} {offset : Nat} {w : B256}
    (value : image.sliceD offset 32 0 = w.toBytes) :
    Bytes.toB256 (image.sliceD offset 32 0) = w := by
  rw [value, B256.toB256_toBytes]

/-- Exact effect of an inbound flow from its auxiliary continuation onward.

The two word parameters are the operation words each flow settles with:
`deposit` supplies `(quote, amount)` and `mint` supplies `(amount, quote)`.
Everything after the quote is shared, including the exact WETH `transferFrom`
child, so both flows reach this one theorem. -/
theorem inboundAfterQuote_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {image : Bytes}
    {sharesWord assetsSourceWord : B256}
    {receiver quote supply shares assets : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (memoryReads : Mem.Reads entry.memory image)
    (receiverAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) =
        receiver)
    (supplyAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
        supply)
    (sharesAt : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (sharesWord * 32).toNat 32 0) = shares)
    (assetsAt : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (assetsSourceWord * 32).toNat 32 0) = assets)
    (sharesAbove : 896 ≤ (sharesWord * 32).toNat)
    (sharesBelow : (sharesWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (assetsAbove : 896 ≤ (assetsSourceWord * 32).toNat)
    (assetsBelow : (assetsSourceWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (supplyStorage :
      supply = Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (stack : quote :: [] <<+ entry.stack)
    (resources : InboundChildResources sevm assetsSourceWord)
    (run : Func.RunCompiledTo fs sevm entry
      (mstoreAt Blanc.ProrataWethVault.quoteWord +++
        Blanc.ProrataWethVault.nonzeroCaller
          (Blanc.ProrataWethVault.nonzeroStagedAddress
            Blanc.ProrataWethVault.receiverWord
            (Blanc.ProrataWethVault.finishInbound
              (Blanc.ProrataWethVault.loadWord sharesWord)
              (Blanc.ProrataWethVault.loadWord assetsSourceWord)
              (Blanc.ProrataWethVault.loadWord
                Blanc.ProrataWethVault.quoteWord)))) (.ok post)) :
    sevm.caller.toB256 ≠ 0 ∧
      ValidAdr receiver ∧
      receiver ≠ 0 ∧
      shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
      InboundEffect sevm receiver assets shares quote entry post := by
  obtain ⟨depth, dynamic, gasAvailable⟩ := resources
  have scratchEnd :
      Blanc.ProrataWethVault.arithmeticScratchEnd = 896 := by decide +kernel
  obtain ⟨guardPre, callerNonzero, receiverValid, receiverNonzero,
      guardStack, guardWf, guardReads, guardState, guardLogs, guardRun⟩ :=
    Blanc.ProrataWethVault.inboundGuards_trace memoryWf memoryReads
      receiverAt stack run
  have guardStorage : Devm.getStor entry = Devm.getStor guardPre :=
    funext (getStor_eq_of_state_eq guardState)
  have guardCode : Devm.getCode entry = Devm.getCode guardPre :=
    funext (getCode_eq_of_state_eq guardState)
  have supplyAtQuote : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) = supply := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact supplyAt
    · right
      decide +kernel
  have receiverAtQuote : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) = receiver := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAt
    · left
      decide +kernel
  have quoteAtQuote : Bytes.toB256
      ((Bytes.writeAt image
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (Blanc.ProrataWethVault.quoteWord * 32).toNat 32 0) = quote :=
    toB256_of_sliceBytes (Bytes.sliceD_writeAt image quote.toBytes _)

  rw [Blanc.ProrataWethVault.finishInbound_shape] at guardRun
  obtain ⟨childEntry, roomFits, childStack, childWf, childReads, childState,
      childLogs, childRun⟩ :=
    Blanc.ProrataWethVault.shareRoomGuard_trace guardWf guardReads sharesAt
      supplyAtQuote stable guardStack guardRun
  have childStorage : Devm.getStor guardPre = Devm.getStor childEntry :=
    funext (getStor_eq_of_state_eq childState)
  have childCode : Devm.getCode guardPre = Devm.getCode childEntry :=
    funext (getCode_eq_of_state_eq childState)

  obtain ⟨callPre, callPost, staging, crossing, suffix⟩ :=
    callWethTransferFrom_trace childRun
  have stagingCode : Devm.getCode childEntry = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
        pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun (guardCode.trans (childCode.trans stagingCode)) wethAccount]
    exact config.code
  obtain ⟨tailPre, movement, childForeign, childLogged, -, tailWf,
      tailWindow, tailRun⟩ :=
    callWethTransferFrom_worldEffect callConfig ⟨childWf, childReads⟩
      (sliceBytes_of_toB256 assetsAt) (by omega) staging depth dynamic
      (gasAvailable childEntry callPre staging) crossing suffix
  have stagingStorage : Devm.getStor childEntry = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by
      unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
        pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have stagingLogs : childEntry.logs = callPre.logs :=
    Line.of_inv Devm.logs (by
      unfold transferFromStaging Blanc.ProrataWethVault.loadWord mstoreAt
        pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have stagingStack : Blanc.Split ([] : Stack) callPre.stack callPre.stack :=
    by simp [Blanc.Split]

  -- Transport every operation word across the calldata frame and the child.
  have tailReads : Mem.Reads tailPre.memory tailPre.memory.data.toList := by
    intro index
    simp
  have carry : ∀ {offset : Nat} {w : B256}, 128 ≤ offset →
      Bytes.toB256
        ((Bytes.writeAt image
            (Blanc.ProrataWethVault.quoteWord * 32).toNat
            quote.toBytes).sliceD offset 32 0) = w →
      Bytes.toB256 (tailPre.memory.data.toList.sliceD offset 32 0) = w := by
    intro offset w above value
    have childWindow : MemWordAt childEntry offset w :=
      MemWordAt.of_memImage ⟨childWf, childReads⟩ (sliceBytes_of_toB256 value)
    exact toB256_of_sliceBytes
      ((tailWindow above childWindow).slice_eq tailReads)

  obtain ⟨balance, balanceEq, noWrap, returned, tailStorage, tailForeign,
      tailLogged⟩ :=
    Blanc.ProrataWethVault.inboundTail_effect tailWf tailReads
      (carry (by decide +kernel) receiverAtQuote)
      (carry (by decide +kernel) supplyAtQuote)
      (carry (by omega) sharesAt)
      (carry (by omega) assetsAt)
      (carry (by decide +kernel) quoteAtQuote)
      (by omega) sharesBelow (by omega) assetsBelow
      (by decide +kernel) (by decide +kernel) nil_pref tailRun

  -- Assemble against the pre-call world.
  have vaultNe : wethAccount ≠ sevm.currentTarget := config.distinct
  have entryToCall : Devm.getStor entry = Devm.getStor callPre :=
    guardStorage.trans (childStorage.trans stagingStorage)
  have entryToTail : ∀ account, wethAccount ≠ account →
      Devm.getStor tailPre account = Devm.getStor entry account := by
    intro account accountNe
    rw [childForeign account accountNe, ← congrFun entryToCall account]
  have vaultStorage :
      Devm.getStor tailPre sevm.currentTarget =
        Devm.getStor entry sevm.currentTarget :=
    entryToTail sevm.currentTarget vaultNe
  have entryLogs : entry.logs = callPre.logs :=
    guardLogs.trans (childLogs.trans stagingLogs)
  have storValEq : ∀ k, Devm.getStorVal tailPre sevm.currentTarget k =
      Devm.getStorVal entry sevm.currentTarget k := by
    intro k
    change (Devm.getStor tailPre sevm.currentTarget).get k =
      (Devm.getStor entry sevm.currentTarget).get k
    rw [vaultStorage]
  refine ⟨callerNonzero, receiverValid, receiverNonzero, roomFits, returned,
    ?_, ?_, ?_, ?_⟩
  · rw [congrFun entryToCall wethAccount,
      tailForeign wethAccount (Ne.symm vaultNe)]
    exact movement
  · rw [tailStorage, balanceEq, storValEq receiver, vaultStorage,
      supplyStorage]
  · intro account wethNe vaultAccountNe
    rw [tailForeign account vaultAccountNe, entryToTail account wethNe]
  · rw [tailLogged, childLogged, ← entryLogs, List.append_assoc]
    rfl

/-- Resources required by the exact WETH asset query that prices an inbound
quote.  Like `InboundChildResources`, the gas obligation is tied to the fixed
staging line that produces the call state. -/
def InboundReadResources (sevm : Sevm) : Prop :=
  sevm.depth ≠ 0 ∧
    ∀ stagingEntry callPre,
      Line.Run sevm stagingEntry balanceOfStaging callPre →
      StaticGasAvailable callPre 36

/-- Shared inbound prefix: stage the two ABI arguments, price the quote from
the booked WETH balance *before* the transfer, stage the exact share supply,
and discharge the stable-supply guard.  The result is the state at which each
flow's own quote arithmetic begins. -/
theorem inboundQuoteStaging_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {arithmetic : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : InboundReadResources sevm)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.arg 0 +++ mstoreAt Blanc.ProrataWethVault.amountWord +++
        Blanc.arg 1 +++ mstoreAt Blanc.ProrataWethVault.receiverWord +++
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
          (Blanc.ProrataWethVault.assetsWord * 32).toNat 32 0) =
        (entry.state.getStor wethAccount).get sevm.currentTarget.toB256 ∧
      Bytes.toB256
        (image.sliceD
          (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) = supply ∧
      [] <<+ quotePre.stack ∧
      Devm.getStor entry = Devm.getStor quotePre ∧
      entry.logs = quotePre.logs ∧
      quotePre.getCode wethAccount = entry.getCode wethAccount ∧
      Func.RunCompiledTo fs sevm quotePre arithmetic (.ok post) := by
  obtain ⟨depth, gasAvailable⟩ := resources
  have entryReads : Mem.Reads entry.memory entry.memory.data.toList := by
    intro index
    simp
  obtain ⟨readPre, readStack, readWf, readReads, argState, argLogs,
      readRun⟩ :=
    Blanc.ProrataWethVault.inboundArgs_trace memoryWf entryReads stack run
  have argStorage : Devm.getStor entry = Devm.getStor readPre :=
    funext (getStor_eq_of_state_eq argState)
  have argCode : Devm.getCode entry = Devm.getCode readPre :=
    funext (getCode_eq_of_state_eq argState)
  have readConfig :
      DirectWethConfiguration sevm.currentTarget sevm readPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun argCode wethAccount]
    exact config.code

  -- Price the quote from the WETH balance booked before the transfer.
  unfold Blanc.ProrataWethVault.snapshotQuoteState at readRun
  obtain ⟨callPre, callPost, staging, crossing, suffix⟩ :=
    readTotalAssets_trace readRun
  have stagingCode : Devm.getCode readPre = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold balanceOfStaging mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun (argCode.trans stagingCode) wethAccount]
    exact config.code
  obtain ⟨assets, stagePre, -, -, stageStorage, stageLogs, returnedWord,
      assetsPrefix, stageWf, stageCode, stageWindow, stageRun⟩ :=
    readTotalAssets_exactEffect callConfig ⟨readWf, readReads⟩ staging depth
      (gasAvailable readPre callPre staging) crossing suffix
  have stagingStorage : Devm.getStor readPre = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by line_inv) staging
  have stagingLogs : readPre.logs = callPre.logs :=
    Line.of_inv Devm.logs (by line_inv) staging
  have stageReads : Mem.Reads stagePre.memory stagePre.memory.data.toList := by
    intro index
    simp
  have carryArg : ∀ {offset : Nat} {w : B256}, 64 ≤ offset →
      Bytes.toB256
        ((Blanc.ProrataWethVault.inboundArgImage entry.memory.data.toList
          (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)).sliceD
            offset 32 0) = w →
      Bytes.toB256 (stagePre.memory.data.toList.sliceD offset 32 0) = w := by
    intro offset w above value
    have readWindow : MemWordAt readPre offset w :=
      MemWordAt.of_memImage ⟨readWf, readReads⟩ (sliceBytes_of_toB256 value)
    exact toB256_of_sliceBytes
      ((stageWindow above readWindow).slice_eq stageReads)

  -- Stage the exact share supply and discharge the stable-supply guard.
  obtain ⟨supply, quotePre, supplyEq, stable, quoteStack, quoteWf,
      quoteReads, quoteStorage, quoteCode, quoteLogs, quoteRun⟩ :=
    Blanc.ProrataWethVault.conversionStaging_trace stageWf stageReads
      assetsPrefix stageRun

  -- Assemble against the endpoint entry.
  have entryStorage : Devm.getStor entry = Devm.getStor quotePre :=
    argStorage.trans (stagingStorage.trans (stageStorage.symm.trans
      quoteStorage))
  have entryLogsAll : entry.logs = quotePre.logs :=
    argLogs.trans (stagingLogs.trans (stageLogs.symm.trans quoteLogs))
  have entryCode : quotePre.getCode wethAccount = entry.getCode wethAccount := by
    rw [← congrFun quoteCode wethAccount, stageCode,
      ← congrFun stagingCode wethAccount, ← congrFun argCode wethAccount]
  have entryToCallStorage : Devm.getStor entry = Devm.getStor callPre :=
    argStorage.trans stagingStorage
  have assetsEq : assets =
      (entry.state.getStor wethAccount).get sevm.currentTarget.toB256 := by
    have bytes := congrArg Bytes.toB256 returnedWord
    simp only [B256.toB256_toBytes] at bytes
    rw [bytes]
    exact (congrArg
      (fun storage : Stor => storage.get sevm.currentTarget.toB256)
      (congrFun entryToCallStorage wethAccount)).symm
  have stageToQuoteStorage :
      Devm.getStor stagePre = Devm.getStor quotePre := quoteStorage
  refine ⟨quotePre,
    Blanc.ProrataWethVault.conversionStagingImage
      stagePre.memory.data.toList assets supply,
    supply, ?_, stable, quoteWf, quoteReads, ?_, ?_, ?_, ?_, quoteStack,
    entryStorage, entryLogsAll, entryCode, quoteRun⟩
  · rw [supplyEq]
    change (Devm.getStor stagePre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor entry sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [entryToCallStorage, ← stageStorage]
  · unfold Blanc.ProrataWethVault.conversionStagingImage
    rw [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact carryArg (by decide +kernel)
        (Blanc.ProrataWethVault.inboundArgImage_amount _ _ _)
    · left
      decide +kernel
    · left
      decide +kernel
  · unfold Blanc.ProrataWethVault.conversionStagingImage
    rw [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact carryArg (by decide +kernel)
        (Blanc.ProrataWethVault.inboundArgImage_receiver _ _ _)
    · left
      decide +kernel
    · left
      decide +kernel
  · rw [← assetsEq]
    unfold Blanc.ProrataWethVault.conversionStagingImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _)
    · right
      decide +kernel
  · unfold Blanc.ProrataWethVault.conversionStagingImage
    exact toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _)

end Blanc.Composition.ProrataWethVault
