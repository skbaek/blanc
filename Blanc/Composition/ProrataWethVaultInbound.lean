import Blanc.ProrataWethVaultInbound
import Blanc.CompiledFixedInvariance
import Blanc.Composition.ProrataWethVaultStaging
import Blanc.LedgerConservation

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
    Blanc.ProrataWethVault.inboundGuards_trace (R := Func.RunOk) memoryWf memoryReads
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
    Blanc.ProrataWethVault.shareRoomGuard_trace (R := Func.RunOk) guardWf guardReads sharesAt
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
    Blanc.ProrataWethVault.inboundTail_effect (R := Func.RunOk) tailWf tailReads
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

/-- Shared inbound prefix: stage the two ABI arguments, price the quote from
the booked WETH balance *before* the transfer, stage the exact share supply,
and discharge the stable-supply guard.  The result is the state at which each
flow's own quote arithmetic begins.

The snapshot itself is `quoteSnapshot_effect`, shared with the outbound flows;
only the argument staging in front of it is inbound-specific. -/
theorem inboundQuoteStaging_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {arithmetic : Func}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : QuoteReadResources sevm)
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
    Blanc.ProrataWethVault.inboundArgs_trace (R := Func.RunOk) memoryWf entryReads stack run
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
      (Blanc.ProrataWethVault.inboundArgImage_amount _ _ _),
    carry (by decide +kernel) (by decide +kernel)
      (Blanc.ProrataWethVault.inboundArgImage_receiver _ _ _),
    ?_, supplyAt, quoteStack, entryStorage, argLogs.trans snapLogs, ?_, ?_,
    quoteRun⟩
  · rw [supplyEq]
    change (Devm.getStor readPre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor entry sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [argStorage]
  · rw [assetsAt]
    exact (congrArg (fun storage : Stor => storage.get sevm.currentTarget.toB256)
      (congrFun argStorage wethAccount)).symm
  · rw [snapCode, ← congrFun argCode wethAccount]
  · change (Devm.getStor entry sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor quotePre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [entryStorage]

/-- An inbound flow preserves ledger conservation: it is a paired mint, one
share row and the supply rising by exactly the same quoted amount.

The supply-side overflow bound is not a premise — it follows from the vault's
own supply-room guard, which is why the contract carries no separate overflow
check on the supply. -/
theorem inboundEffect_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    {receiver assets shares returned supply : B256}
    (receiverValid : ValidAdr receiver)
    (supplyEq : supply = Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (roomFits : shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat)
    (effect : InboundEffect sevm receiver assets shares returned pre post)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨-, -, vaultStorage, -, -⟩ := effect
  obtain ⟨receiverAdr, receiverAdrEq⟩ := receiverValid
  have overflow : B256.Nof
      ((Devm.getStor pre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot) shares := by
    have supplyNat : supply.toNat =
        ((Devm.getStor pre sevm.currentTarget).get
          Blanc.ProrataWethVault.supplySlot).toNat :=
      congrArg B256.toNat supplyEq
    have room : Blanc.ProrataWethVault.shareRoomN supply.toNat =
        Blanc.ProrataWethVault.maxSupplyN - supply.toNat := rfl
    have maxLt : Blanc.ProrataWethVault.maxSupplyN < 2 ^ 256 := by
      unfold Blanc.ProrataWethVault.maxSupplyN maxWordN wordModulusN
      omega
    unfold B256.Nof
    rw [room] at roomFits
    omega
  rw [vaultStorage, ← receiverAdrEq]
  exact conserved.mint_set Blanc.ProrataWethVault.supplySlot_not_validAdr
    overflow

/-- Join one flow's quote arithmetic to the shared settlement.

`sharesWord` and `assetsSourceWord` are the operation words the flow settles
with, `quote` is the word its arithmetic produced, and `quoteFrame` is that
arithmetic's frame: it left the world and the log alone, so the settlement's
conclusions can be stated against the endpoint entry rather than against some
mid-body state. -/
theorem inboundBody_effect
    {fs : List Func} {sevm : Sevm} {entry quotePre afterPre post : Devm}
    {image afterImage : Bytes}
    {sharesWord assetsSourceWord receiver quote supply shares assets : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (entryStorage : Devm.getStor entry = Devm.getStor quotePre)
    (entryLogs : entry.logs = quotePre.logs)
    (entryCode : quotePre.getCode wethAccount = entry.getCode wethAccount)
    (supplyProjection :
      Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot =
      Devm.getStorVal quotePre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot)
    (supplyEq : supply = Devm.getStorVal entry sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (receiverAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.receiverWord * 32).toNat 32 0) =
        receiver)
    (supplyAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
        supply)
    (afterMemImage : MemImage afterPre afterImage)
    (afterFrame : Bytes.WordFrameFrom image afterImage
      Blanc.ProrataWethVault.arithmeticScratchEnd)
    (quoteFrame : Devm.QuietFrame quotePre afterPre)
    (afterStack : quote :: [] <<+ afterPre.stack)
    (sharesAt : Bytes.toB256
      ((Bytes.writeAt afterImage
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (sharesWord * 32).toNat 32 0) = shares)
    (assetsAt : Bytes.toB256
      ((Bytes.writeAt afterImage
          (Blanc.ProrataWethVault.quoteWord * 32).toNat quote.toBytes).sliceD
        (assetsSourceWord * 32).toNat 32 0) = assets)
    (sharesAbove : 896 ≤ (sharesWord * 32).toNat)
    (sharesBelow : (sharesWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (assetsAbove : 896 ≤ (assetsSourceWord * 32).toNat)
    (assetsBelow : (assetsSourceWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (resources : InboundChildResources sevm assetsSourceWord)
    (afterRun : Func.RunCompiledTo fs sevm afterPre
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
  obtain ⟨callerNonzero, receiverValid, receiverNonzero, roomFits, returned,
      movement, vaultStorage, foreign, logged⟩ :=
    inboundAfterQuote_effect afterConfig afterMemImage.1 afterMemImage.2
      (carry (by decide +kernel) receiverAt)
      (carry (by decide +kernel) supplyAt)
      sharesAt assetsAt sharesAbove sharesBelow assetsAbove assetsBelow
      (by
        rw [supplyEq, supplyProjection]
        change (Devm.getStor quotePre sevm.currentTarget).get
            Blanc.ProrataWethVault.supplySlot =
          (Devm.getStor afterPre sevm.currentTarget).get
            Blanc.ProrataWethVault.supplySlot
        rw [funext (getStor_eq_of_state_eq quoteFrame.1)])
      stable afterStack resources afterRun
  have quoteStorage : Devm.getStor quotePre = Devm.getStor afterPre :=
    funext (getStor_eq_of_state_eq quoteFrame.1)
  have storValEq : ∀ k, Devm.getStorVal entry sevm.currentTarget k =
      Devm.getStorVal afterPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor entry sevm.currentTarget).get k =
      (Devm.getStor afterPre sevm.currentTarget).get k
    rw [congrFun entryStorage sevm.currentTarget,
      congrFun quoteStorage sevm.currentTarget]
  refine ⟨callerNonzero, receiverValid, receiverNonzero, roomFits, returned,
    ?_, ?_, ?_, ?_⟩
  · rw [congrFun entryStorage wethAccount, congrFun quoteStorage wethAccount]
    exact movement
  · rw [congrFun entryStorage sevm.currentTarget,
      congrFun quoteStorage sevm.currentTarget, storValEq receiver,
      storValEq Blanc.ProrataWethVault.supplySlot]
    exact vaultStorage
  · intro account wethNe vaultNe
    rw [foreign account wethNe vaultNe, ← congrFun quoteStorage account,
      ← congrFun entryStorage account]
  · rw [logged, ← quoteFrame.2, ← entryLogs]

/-- Exact compiled body effect of `deposit(assets, receiver)`.

The minted share amount is the exact G1 full-width floor conversion
`floor(assets * D / X)` taken from the WETH balance booked *before* the
inbound transfer and the pre-state share supply.  It fits one word, the caller
and receiver pass their guards, it fits the remaining supply room, and the
flow's complete observable effect is `InboundEffect`. -/
theorem deposit_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (readResources : QuoteReadResources sevm)
    (childResources :
      InboundChildResources sevm Blanc.ProrataWethVault.amountWord)
    (lookup : fs[Blanc.ProrataWethVault.depositAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.depositAfterQuote)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      Blanc.ProrataWethVault.deposit (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.convertToSharesN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      Sevm.argWord sevm 1 ≠ 0 ∧
      (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤
        Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
      InboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 0)
        (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        entry post := by
  rw [Blanc.ProrataWethVault.deposit_shape] at run
  obtain ⟨quotePre, image, supply, supplyEq, stable, quoteWf, quoteReads,
      amountAt, receiverAt, assetsAt, supplyAt, quoteStack, quoteStorage,
      quoteLogs, quoteCode, supplyProjection, quoteRun⟩ :=
    inboundQuoteStaging_effect config memoryWf readResources stack run
  obtain ⟨quoteFits, afterPre, afterImage, afterStack, afterMemImage,
      afterFrame, quoteFrame, afterRun⟩ :=
    Blanc.ProrataWethVault.depositQuote_arithmetic_trace (R := Func.RunOk) quoteWf quoteReads
      amountAt assetsAt supplyAt stable quoteStack lookup quoteRun
  rw [Blanc.ProrataWethVault.depositAfterQuote_shape] at afterRun
  have amountAtAfter : Bytes.toB256
      (afterImage.sliceD
        (Blanc.ProrataWethVault.amountWord * 32).toNat 32 0) =
        Sevm.argWord sevm 0 := by
    rw [afterFrame _ (by decide +kernel)]
    exact amountAt
  obtain ⟨callerNonzero, receiverValid, receiverNonzero, roomFits, effect⟩ :=
    inboundBody_effect config quoteStorage quoteLogs quoteCode
      supplyProjection supplyEq stable receiverAt supplyAt afterMemImage
      afterFrame quoteFrame afterStack
      (shares := Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat))
      (assets := Sevm.argWord sevm 0)
      (toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _))
      (by
        rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _
          (Or.inl (by decide +kernel))]
        exact amountAtAfter)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) childResources afterRun
  exact ⟨supply, supplyEq, stable, quoteFits, callerNonzero, receiverValid,
    receiverNonzero, roomFits, effect⟩

/-- Exact compiled body effect of `mint(shares, receiver)`.

The charged asset amount is the exact G1 full-width ceiling conversion
`ceil(shares * X / D)` taken from the pre-transfer booked balance and the
pre-state share supply; the minted share amount is exactly the requested one,
and the returned word is the charged assets. -/
theorem mint_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (readResources : QuoteReadResources sevm)
    (childResources :
      InboundChildResources sevm Blanc.ProrataWethVault.quoteWord)
    (lookup : fs[Blanc.ProrataWethVault.mintAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.mintAfterQuote)
    (stack : [] <<+ entry.stack)
    (run : Func.RunCompiledTo fs sevm entry
      Blanc.ProrataWethVault.mint (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot ∧
      supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
      Blanc.ProrataWethVault.previewMintN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      Sevm.argWord sevm 1 ≠ 0 ∧
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
      InboundEffect sevm (Sevm.argWord sevm 1)
        (Nat.toB256 (Blanc.ProrataWethVault.previewMintN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        (Sevm.argWord sevm 0)
        (Nat.toB256 (Blanc.ProrataWethVault.previewMintN
          (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat))
        entry post := by
  rw [Blanc.ProrataWethVault.mint_shape] at run
  obtain ⟨quotePre, image, supply, supplyEq, stable, quoteWf, quoteReads,
      amountAt, receiverAt, assetsAt, supplyAt, quoteStack, quoteStorage,
      quoteLogs, quoteCode, supplyProjection, quoteRun⟩ :=
    inboundQuoteStaging_effect config memoryWf readResources stack run
  obtain ⟨quoteFits, afterPre, afterImage, afterStack, afterMemImage,
      afterFrame, quoteFrame, afterRun⟩ :=
    Blanc.ProrataWethVault.mintQuote_arithmetic_trace (R := Func.RunOk) quoteWf quoteReads
      amountAt assetsAt supplyAt stable quoteStack lookup quoteRun
  rw [Blanc.ProrataWethVault.mintAfterQuote_shape] at afterRun
  have amountAtAfter : Bytes.toB256
      (afterImage.sliceD
        (Blanc.ProrataWethVault.amountWord * 32).toNat 32 0) =
        Sevm.argWord sevm 0 := by
    rw [afterFrame _ (by decide +kernel)]
    exact amountAt
  obtain ⟨callerNonzero, receiverValid, receiverNonzero, roomFits, effect⟩ :=
    inboundBody_effect config quoteStorage quoteLogs quoteCode
      supplyProjection supplyEq stable receiverAt supplyAt afterMemImage
      afterFrame quoteFrame afterStack
      (shares := Sevm.argWord sevm 0)
      (assets := Nat.toB256 (Blanc.ProrataWethVault.previewMintN
        (Sevm.argWord sevm 0).toNat
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat))
      (by
        rw [Bytes.readWord_writeAt_of_disjoint _ _ _ _
          (Or.inl (by decide +kernel))]
        exact amountAtAfter)
      (toB256_of_sliceBytes (Bytes.sliceD_writeAt _ _ _))
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) childResources afterRun
  exact ⟨supply, supplyEq, stable, quoteFits, callerNonzero, receiverValid,
    receiverNonzero, roomFits, effect⟩

/-! ## Public compiled selectors -/

/-- Persistent-state and log equality is enough to move a whole inbound
observation from a body entry back to the message entry. -/
private theorem inboundEffect_lift {sevm : Sevm} {pre bodyPre post : Devm}
    {receiver assets shares returned : B256}
    (entryState : pre.state = bodyPre.state)
    (entryLogs : pre.logs = bodyPre.logs)
    (effect :
      InboundEffect sevm receiver assets shares returned bodyPre post) :
    InboundEffect sevm receiver assets shares returned pre post := by
  obtain ⟨output, movement, vaultStorage, foreign, logged⟩ := effect
  have storage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have storVal : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal bodyPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor bodyPre sevm.currentTarget).get k
    rw [congrFun storage sevm.currentTarget]
  refine ⟨output, ?_, ?_, ?_, ?_⟩
  · rw [congrFun storage wethAccount]
    exact movement
  · rw [congrFun storage sevm.currentTarget, storVal receiver,
      storVal Blanc.ProrataWethVault.supplySlot]
    exact vaultStorage
  · intro account wethNe vaultNe
    rw [foreign account wethNe vaultNe, ← congrFun storage account]
  · rw [logged, ← entryLogs]

private theorem depositAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.depositAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.depositAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.depositAfterQuoteSlot]

private theorem mintAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
      Blanc.ProrataWethVault.vault.aux)[
        Blanc.ProrataWethVault.mintAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.mintAfterQuote := by
  simp [Blanc.ProrataWethVault.vault, Blanc.ProrataWethVault.vaultAux,
    Blanc.ProrataWethVault.mintAfterQuoteSlot]

private theorem deposit_mem_vaultFuncs :
    (selector "deposit" [.uint256, .address],
      Blanc.ProrataWethVault.routed 2 Blanc.ProrataWethVault.deposit) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

private theorem mint_mem_vaultFuncs :
    (selector "mint" [.uint256, .address],
      Blanc.ProrataWethVault.routed 2 Blanc.ProrataWethVault.mint) ∈
      Blanc.ProrataWethVault.vaultFuncs := by
  simp [Blanc.ProrataWethVault.vaultFuncs]

/-- Resources for a compiled inbound endpoint, tied to the exact selector's
body rather than asserted for every state. -/
def InboundCompiledResources (sevm : Sevm) (assetsSourceWord : B256) : Prop :=
  QuoteReadResources sevm ∧ InboundChildResources sevm assetsSourceWord

/-- Public compiled `deposit(assets, receiver)`.

The vault acquires exactly `assets` WETH from the caller through the exact
configured `transferFrom` child, mints exactly `floor(assets * D / X)` shares
against the balance booked before that transfer, credits the receiver,
increases the supply, emits the child's `Transfer` then the share `Transfer`
then `Deposit`, and returns the minted shares.  No other account's storage
moves. -/
theorem deposit_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources :
      InboundCompiledResources sevm Blanc.ProrataWethVault.amountWord)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "deposit" [.uint256, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.convertToSharesN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat)).toNat ≤
          Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
        InboundEffect sevm (Sevm.argWord sevm 1) (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          (Nat.toB256 (Blanc.ProrataWethVault.convertToSharesN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          pre post := by
  rcases Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs
      run selectorEq deposit_mem_vaultFuncs with
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
      receiverNonzero, roomFits, effect⟩ :=
    deposit_body_effect bodyConfig bodyWf resources.1 resources.2
      depositAfterQuote_lookup nil_pref bodyRun
  refine ⟨valueZero, supply, ?_, stable, ?_, callerNonzero, receiverValid,
    receiverNonzero, ?_, ?_⟩
  · rw [supplyEq]
    change (Devm.getStor bodyPre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor pre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [funext (getStor_eq_of_state_eq entryState)]
  · rw [← entryState] at quoteFits
    exact quoteFits
  · rw [← entryState] at roomFits
    exact roomFits
  · rw [← entryState] at effect
    exact inboundEffect_lift entryState entryLogs effect

/-- Public compiled `mint(shares, receiver)`. -/
theorem mint_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources :
      InboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "mint" [.uint256, .address]) :
    sevm.value = 0 ∧
      ∃ supply,
        supply = Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot ∧
        supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN ∧
        Blanc.ProrataWethVault.previewMintN (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
        sevm.caller.toB256 ≠ 0 ∧
        ValidAdr (Sevm.argWord sevm 1) ∧
        Sevm.argWord sevm 1 ≠ 0 ∧
        (Sevm.argWord sevm 0).toNat ≤
          Blanc.ProrataWethVault.shareRoomN supply.toNat ∧
        InboundEffect sevm (Sevm.argWord sevm 1)
          (Nat.toB256 (Blanc.ProrataWethVault.previewMintN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          (Sevm.argWord sevm 0)
          (Nat.toB256 (Blanc.ProrataWethVault.previewMintN
            (Sevm.argWord sevm 0).toNat
            ((pre.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat))
          pre post := by
  rcases Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs
      run selectorEq mint_mem_vaultFuncs with
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
      receiverNonzero, roomFits, effect⟩ :=
    mint_body_effect bodyConfig bodyWf resources.1 resources.2
      mintAfterQuote_lookup nil_pref bodyRun
  refine ⟨valueZero, supply, ?_, stable, ?_, callerNonzero, receiverValid,
    receiverNonzero, roomFits, ?_⟩
  · rw [supplyEq]
    change (Devm.getStor bodyPre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot =
      (Devm.getStor pre sevm.currentTarget).get
        Blanc.ProrataWethVault.supplySlot
    rw [funext (getStor_eq_of_state_eq entryState)]
  · rw [← entryState] at quoteFits
    exact quoteFits
  · rw [← entryState] at effect
    exact inboundEffect_lift entryState entryLogs effect


/-! ## Conservation at the public inbound endpoints

Each is `inboundEffect_preserves_conserved` after the compiled effect.  The
`DirectWethConfiguration` premise is not incidental: the flow snapshots the
supply before the WETH child and writes it after, so conservation across the
frame depends on that child not re-entering the vault, which is exactly what
pinning the asset's code buys.  See `Blanc/ProrataWethVaultLedgerSpec.lean`. -/

theorem deposit_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources :
      InboundCompiledResources sevm Blanc.ProrataWethVault.amountWord)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "deposit" [.uint256, .address])
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨-, supply, supplyEq, stable, -, -, receiverValid, -, roomFits,
      effect⟩ :=
    deposit_compiled_effect config memoryWf resources run selectorEq
  exact inboundEffect_preserves_conserved receiverValid supplyEq stable
    roomFits effect conserved

theorem mint_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources :
      InboundCompiledResources sevm Blanc.ProrataWethVault.quoteWord)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (selectorEq :
      Sevm.selector sevm = selector "mint" [.uint256, .address])
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor pre sevm.currentTarget)) :
    LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨-, supply, supplyEq, stable, -, -, receiverValid, -, roomFits,
      effect⟩ :=
    mint_compiled_effect config memoryWf resources run selectorEq
  exact inboundEffect_preserves_conserved receiverValid supplyEq stable
    roomFits effect conserved
end Blanc.Composition.ProrataWethVault
