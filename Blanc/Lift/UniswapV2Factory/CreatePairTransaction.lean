import Blanc.Lift.UniswapV2Factory.CreatePairFrame
import Blanc.Lift.UniswapV2Factory.Check
import Blanc.Lift.UniswapV2Factory.Jumps
import Blanc.Lift.UniswapV2Pair.CreationTransaction
import Blanc.CodeDelegation

/-!
# The recorded `createPair` transaction settles the initialized Pair

`pair_createPair_transaction_muirGlacier`: a legacy transaction to the Uniswap V2 factory with
the recorded calldata `createPair(WETH, USDC)` (Pair creation transaction `0xd07c…ab3a`, index 38
of block 10,008,355, whose fork the mainnet schedule selects as Muir Glacier, `pair_deployment_fork`),
zero value and the recorded nonce 205, admitted by Jaune's own validation and admission checks, with
the sender able to pay `gas × price` and at least 2,600,000 gas beyond the intrinsic charge, over a
pre-state that holds the certified factory runtime at the factory (nonce below the maximum), an empty
Pair `CREATE2` address, and no `getPair` entry for the two tokens in either direction, succeeds
through `processTransaction`, and the settled state holds the certified Pair runtime at the Pair
address with storage at the initialized checkpoint over the factory, the domain separator of the
block's chain id and the Pair address, and the sorted tokens (USDC, WETH).

The message call is the factory frame of `createPair_frame`; its settlement is
`pair_creation_transaction_settles_muirGlacier`. No token contract is called by `createPair`, so the
statement takes no premise about the tokens' code. The recorded transaction's gas (3,770,079), gas
price (4 gwei) and sender are not written here: the gas is any amount meeting the bound, and the
sender is the one Jaune's admission check recovers.
-/

namespace Blanc.Lift.UniswapV2Factory

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift

/-- **The recorded `createPair` transaction settles the initialized Pair.**  In a block whose fork
the mainnet schedule selects at the recorded Pair creation coordinates, a legacy transaction to the
factory with the recorded `createPair(WETH, USDC)` calldata, zero value and nonce 205, which Jaune
validates and admits, whose sender can pay `gas × price`, and whose gas covers the intrinsic charge
plus 2,600,000 (below `2^64`), over a state holding the certified factory runtime at the factory
(nonce below the maximum), an empty Pair `CREATE2` address and no `getPair` entry for the two
tokens in either direction, is processed by `processTransaction`; the settled state holds the
certified Pair runtime at the Pair address with storage at the initialized checkpoint. -/
theorem pair_createPair_transaction_muirGlacier
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {gasPrice intrinsicGas calldataFloorGas effectiveGasPrice : Nat} {sender : Adr}
    {blobVersionedHashes : List B256} {txBlobGasUsed : Nat}
    (hfork : mainnetChainConfig.forkAt 10008355 1588710145 = .ok benv.stat.fork)
    (htype : tx.type = .zero gasPrice (some UniswapV2Pair.Creation.factory))
    (hdata : tx.data = createPairData) (hvalue : tx.value = 0) (hnonce : tx.nonce = 205)
    (hvalid : validateTransaction benv.stat.rules tx 0 = .ok (intrinsicGas, calldataFloorGas))
    (hchecked : checkTransaction benv.beginTransaction
      (ExecutionTrace.transactionPreludeBout bout tx index) tx =
        .ok (sender, effectiveGasPrice, blobVersionedHashes, txBlobGasUsed))
    (hfunds : (tx.gas * effectiveGasPrice).toB256 ≤ benv.state.bal sender)
    (hgas : intrinsicGas + 2600000 ≤ tx.gas) (hgasb : tx.gas < 2 ^ 64)
    (hfactory : benv.state.getCode UniswapV2Pair.Creation.factory = code)
    (hfnonce : (benv.state.get UniswapV2Pair.Creation.factory).nonce ≠ UInt64.max)
    (hpairNonce : (benv.state.get UniswapV2Pair.Creation.pairAddress).nonce = 0)
    (hpairCode : (benv.state.get UniswapV2Pair.Creation.pairAddress).code.size = 0)
    (hpairStor : (benv.state.get UniswapV2Pair.Creation.pairAddress).stor.size = 0)
    (hslot2 : (benv.state.get UniswapV2Pair.Creation.factory).stor.get fk2 = 0)
    (hslot5 : (benv.state.get UniswapV2Pair.Creation.factory).stor.get fk5 = 0) :
    ∃ post bout', processTransaction benv bout tx index = .ok (post, bout') ∧
      (post.getCode UniswapV2Pair.Creation.pairAddress).toList = UniswapV2Pair.code.toList ∧
      UniswapV2Pair.InitializedCheckpoint (post.getStor UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.factory
        (UniswapV2Pair.Creation.domainSeparator benv.stat.chainId.toB256
          UniswapV2Pair.Creation.pairAddress)
        UniswapV2Pair.Creation.token0 UniswapV2Pair.Creation.token1 := by
  have hmuir : benv.stat.fork = .muirGlacier :=
    Except.ok.inj (hfork.symm.trans UniswapV2Pair.pair_deployment_fork)
  have hrules : benv.stat.rules = Fork.ruleSet .muirGlacier := by rw [BenvStat.rules, hmuir]
  have hsg : benv.stat.rules.stateGas = none := by rw [hrules]; rfl
  have hcodeSize : code.size = 13859 := by
    rw [ByteArray.size_eq_length_toList]; exact code_toList_length
  -- The sender holds no code (delegation is disabled under Muir Glacier), so it is not the factory.
  have hsenderCode : (benv.state.get sender).code.isEmpty = true :=
    checkTransaction_sender_code_emptyH (benv := benv.beginTransaction)
      (by show benv.stat.rules.delegationEnabled = false; rw [hrules]; rfl) hchecked
  have hneF : sender ≠ UniswapV2Pair.Creation.factory := by
    intro h
    rw [h] at hsenderCode
    have hz : (benv.state.get UniswapV2Pair.Creation.factory).code.size = 0 := by
      simpa only [ByteArray.isEmpty, beq_iff_eq] using hsenderCode
    have hc : (benv.state.get UniswapV2Pair.Creation.factory).code = code := hfactory
    rw [hc, hcodeSize] at hz
    exact absurd hz (by decide)
  -- The sender's nonce is 205, so it is not the empty Pair address.
  have hsenderNonce : (benv.state.get sender).nonce = 205 := by
    rw [← hnonce]; exact ExecutionTrace.checkTransaction_sender_nonce hchecked
  have hneP : sender ≠ UniswapV2Pair.Creation.pairAddress := by
    intro h
    rw [h, hpairNonce] at hsenderNonce
    exact absurd hsenderNonce (by decide)
  have hblob : ExecutionTrace.transactionBlobGasFee benv tx = 0 := by
    simp only [ExecutionTrace.transactionBlobGasFee, Tx.isTypeThree, htype, Bool.false_eq_true,
      ↓reduceIte]
  have hdebit : (benv.state.incrNonce sender).subBal sender
      (tx.gas * effectiveGasPrice + ExecutionTrace.transactionBlobGasFee benv tx).toB256 =
      some ((benv.state.incrNonce sender).setBal sender
        (benv.state.bal sender - (tx.gas * effectiveGasPrice).toB256)) := by
    rw [hblob, Nat.add_zero]
    exact subBal_incrNonce_of_le hfunds
  set debit := (benv.state.incrNonce sender).setBal sender
    (benv.state.bal sender - (tx.gas * effectiveGasPrice).toB256) with hdebitDef
  have hdebitF : debit.get UniswapV2Pair.Creation.factory =
      benv.state.get UniswapV2Pair.Creation.factory := debit_get_ne hneF
  have hdebitP : debit.get UniswapV2Pair.Creation.pairAddress =
      benv.state.get UniswapV2Pair.Creation.pairAddress := debit_get_ne hneP
  set msg := callMessage { benv.beginTransaction with state := debit }
    (ExecutionTrace.transactionTenv benv.beginTransaction tx index sender effectiveGasPrice
      intrinsicGas blobVersionedHashes) tx UniswapV2Pair.Creation.factory with hmsgDef
  have hprepared : prepareMessage { benv.beginTransaction with state := debit }
      (ExecutionTrace.transactionTenv benv.beginTransaction tx index sender effectiveGasPrice
        intrinsicGas blobVersionedHashes) tx = .ok msg :=
    prepareMessage_call (by rw [htype]; rfl)
  have hmsgValue : msg.value = 0 := by show tx.value.toB256 = 0; rw [hvalue]; rfl
  have hmsgCode : msg.code = code := by
    show (debit.get UniswapV2Pair.Creation.factory).code = code
    rw [hdebitF]; exact hfactory
  have hmsgRules : msg.benv.stat.rules = Fork.ruleSet .muirGlacier := hrules
  have hentry : msg.benvAfterTransfer = .ok msg.benv := Msg.benvAfterTransfer_of_value_zero hmsgValue
  -- The factory frame, from the message's initial machine.
  obtain ⟨post, hrun, herr, hcodeP, hinit, hatd, hrc⟩ :=
    createPair_frame (sevm := initSevm msg) (b := initDevm msg) (G0 := msg.gas)
      hmuir hmsgCode rfl hmsgValue hdata rfl (show (1024 : Nat) ≠ 0 by decide)
      (by show (debit.get UniswapV2Pair.Creation.factory).code = code; rw [hdebitF]; exact hfactory)
      (by
        show (debit.get UniswapV2Pair.Creation.pairAddress).nonce = 0 ∧
          (debit.get UniswapV2Pair.Creation.pairAddress).code.size = 0 ∧
          (debit.get UniswapV2Pair.Creation.pairAddress).stor.size = 0
        rw [hdebitP]; exact ⟨hpairNonce, hpairCode, hpairStor⟩)
      (by show (debit.get UniswapV2Pair.Creation.factory).nonce ≠ _; rw [hdebitF]; exact hfnonce)
      (by show (debit.get UniswapV2Pair.Creation.factory).stor.get fk2 = 0; rw [hdebitF]; exact hslot2)
      (by show (debit.get UniswapV2Pair.Creation.factory).stor.get fk5 = 0; rw [hdebitF]; exact hslot5)
      (fun k => by
        show (benv.state.get UniswapV2Pair.Creation.factory).stor.get k =
          (debit.get UniswapV2Pair.Creation.factory).stor.get k
        rw [hdebitF])
      (by show 2600000 ≤ tx.gas - intrinsicGas; omega)
      (by show tx.gas - intrinsicGas < 2 ^ 64; omega)
  have hpre : St (initDevm msg) [] Mem.empty msg.gas = initDevm msg := (St.self rfl rfl).symm
  rw [hpre] at hrun
  obtain ⟨exc⟩ := lift_exact_noStateGas cert_check jumps_ok hmsgCode hsg hrun
  have hexec : exec (initEvm (msg.withBenv msg.benv)) = .ok post :=
    (exec_iff_exec_eq _ _ _ _).mp ⟨exc⟩
  have herr0 : post.error = none := herr
  have hprocess := processMessage_call_of_execH hentry rfl
    (by rw [hmsgRules]; decide +kernel) hexec herr0
  have hrc0 : 0 ≤ post.refundCounter := hrc (le_refl _)
  have hcall := processMessageCall_call_of_message hsg rfl
    (by show tx.auths.isEmpty = true; unfold Tx.auths; rw [htype]; rfl)
    (by rw [hmsgCode]; exact getDelegatedCodeAddress_eq_none_of_size_ne (by rw [hcodeSize]; decide))
    hprocess (by rw [Devm.recordTouch_error]; exact herr0)
    (Int.toNat?_eq_some_of_nonneg (by rw [(recordTouch_meta _ _ _ _).2.1]; exact hrc0))
  obtain ⟨settled, bout', htx, hc, hs⟩ := UniswapV2Pair.pair_creation_transaction_settles_muirGlacier
    hfork hvalid hchecked hdebit hprepared hcall
    (Int.toNat?_eq_some_of_nonneg (Int.natCast_nonneg _))
    (by rw [Devm.recordTouch_state]; exact hcodeP)
    (by rw [Devm.recordTouch_state]; exact hinit)
    (by
      show UniswapV2Pair.Creation.pairAddress ∉
        (post.recordTouch msg.benv.stat.rules true msg.currentTarget).accountsToDelete
      rw [(recordTouch_meta _ _ _ _).1]
      exact hatd (Std.HashSet.not_mem_emptyWithCapacity))
  exact ⟨settled, bout', htx, hc, hs⟩

end Blanc.Lift.UniswapV2Factory
