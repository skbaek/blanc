-- Semantics.lean : formalized semantics of the EVM and Blanc

import Blanc.Basic
import Elevm.Hash
import Elevm.Execution



def Rinst.toB8 : Rinst → B8
  | add          => 0x01
  | mul          => 0x02
  | sub          => 0x03
  | div          => 0x04
  | sdiv         => 0x05
  | mod          => 0x06
  | smod         => 0x07
  | addmod       => 0x08
  | mulmod       => 0x09
  | exp          => 0x0A
  | signextend   => 0x0B
  | lt           => 0x10
  | gt           => 0x11
  | slt          => 0x12
  | sgt          => 0x13
  | eq           => 0x14
  | iszero       => 0x15
  | and          => 0x16
  | or           => 0x17
  | xor          => 0x18
  | not          => 0x19
  | byte         => 0x1A
  | shl          => 0x1B
  | shr          => 0x1C
  | sar          => 0x1D
  | kec          => 0x20
  | address      => 0x30
  | balance      => 0x31
  | origin       => 0x32
  | caller       => 0x33
  | callvalue    => 0x34
  | calldataload => 0x35
  | calldatasize => 0x36
  | calldatacopy => 0x37
  | codesize     => 0x38
  | codecopy     => 0x39
  | gasprice     => 0x3A
  | extcodesize  => 0x3B
  | extcodecopy  => 0x3C
  | retdatasize  => 0x3D
  | retdatacopy  => 0x3E
  | extcodehash  => 0x3F
  | blockhash    => 0x40
  | coinbase     => 0x41
  | timestamp    => 0x42
  | number       => 0x43
  | prevrandao   => 0x44
  | gaslimit     => 0x45
  | chainid      => 0x46
  | selfbalance  => 0x47
  | basefee      => 0x48
  | blobhash     => 0x49
  | blobbasefee  => 0x4A
  | pop          => 0x50
  | mload        => 0x51
  | mstore       => 0x52
  | mstore8      => 0x53
  | sload        => 0x54
  | sstore       => 0x55
  | pc           => 0x58
  | msize        => 0x59
  | gas          => 0x5A
  | tload        => 0x5C
  | tstore       => 0x5D
  | mcopy        => 0x5E
  | dup n        => 0x80 + n.val.toUInt8
  | swap n       => 0x90 + n.val.toUInt8
  | log n        => 0xA0 + n.val.toUInt8

abbrev Stack : Type := List B256

def Stack.Push (x y xy : Stack) : Prop := x <++ xy ++> y
def Stack.Pop (x xy y : Stack) : Prop := x <++ xy ++> y
-- def Stack.Diff (xs zs : Stack) (s s'' : Stack) : Prop :=
--   ∃ s' : Stack, Pop xs s s' ∧ Push zs s' s''

inductive Func : Type
  | branch : Func → Func → Func
  | last : Linst → Func
  | next : Ninst → Func → Func
  | call : Nat → Func

structure Prog : Type where
  (main : Func)
  (aux : List Func)

def Jinst.Run (evm : Evm) :
    Jinst → Except (String × Devm) (Nat × Devm) → Prop :=
  λ j ex => j.run evm = ex

def Linst.Run (sevm : Sevm) (devm : Devm) : Linst → Execution → Prop :=
  λ l ex => l.run sevm devm = ex

def Xlot : Type := Option (Evm × Execution)

structure Devm.Rels : Type where
  (stack : List B256 → List B256 → Prop)
  (memory : Mem → Mem → Prop)
  (gasLeft : Nat → Nat → Prop)
  (logs : List Log → List Log → Prop)
  (refundCounter : Int → Int → Prop)
  (output : B8L → B8L → Prop)
  (accountsToDelete : AdrSet → AdrSet → Prop)
  (returnData : B8L → B8L → Prop)
  (error : Option String → Option String → Prop)
  (accessedAddresses : AdrSet → AdrSet → Prop)
  (accessedStorageKeys : KeySet → KeySet → Prop)
  (state : State → State → Prop)
  (createdAccounts : AdrSet → AdrSet → Prop)
  (transientStorage : Tra → Tra → Prop)

structure Devm.Rel (rels : Devm.Rels) (devm devm' : Devm) : Prop where
  (stack : rels.stack devm.stack devm'.stack)
  (memory : rels.memory devm.memory devm'.memory)
  (gasLeft : rels.gasLeft devm.gasLeft devm'.gasLeft)
  (logs : rels.logs devm.logs devm'.logs)
  (refundCounter : rels.refundCounter devm.refundCounter devm'.refundCounter)
  (output : rels.output devm.output devm'.output)
  ( accountsToDelete :
    rels.accountsToDelete devm.accountsToDelete devm'.accountsToDelete)
  (returnData : rels.returnData devm.returnData devm'.returnData)
  (error : rels.error devm.error devm'.error)
  ( accessedAddresses :
    rels.accessedAddresses devm.accessedAddresses devm'.accessedAddresses )
  ( accessedStorageKeys :
    rels.accessedStorageKeys devm.accessedStorageKeys devm'.accessedStorageKeys )
  (state : rels.state devm.state devm'.state)
  ( transientStorage :
    rels.transientStorage devm.transientStorage devm'.transientStorage )

def Devm.Rels.eq : Devm.Rels :=
  {
    stack := _root_.Eq,
    memory := _root_.Eq,
    gasLeft := _root_.Eq,
    logs := _root_.Eq,
    refundCounter := _root_.Eq,
    output := _root_.Eq,
    accountsToDelete := _root_.Eq,
    returnData := _root_.Eq,
    error := _root_.Eq,
    accessedAddresses := _root_.Eq,
    accessedStorageKeys := _root_.Eq,
    state := _root_.Eq,
    createdAccounts := _root_.Eq,
    transientStorage := _root_.Eq
  }

def Devm.Burn : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    gasLeft := (· ≥ · )
  }

lemma Nat.le_iff_exists (m n : Nat) : m ≤ n ↔ ∃ k, n = m + k := by
  constructor
  · intro _
    exists n - m
    omega
  · rintro ⟨k, hk⟩
    omega


def Devm.PopBurn (xs : List B256) : Devm → Devm → Prop :=
  Rel {
    Rels.eq with
    stack := Stack.Pop xs
    gasLeft := (· ≥ ·)
      -- λ gas gas' => ∃ diff : Nat, gas = gas' + diff
  }

def Linst.At (code : ByteArray) (pc : Nat) (l : Linst) : Prop := code.getInst pc = some (.last l)
def Ninst.At (code : ByteArray) (pc : Nat) (n : Ninst) : Prop := code.getInst pc = some (.next n)
def Jinst.At (code : ByteArray) (pc : Nat) (j : Jinst) : Prop := code.getInst pc = some (.jump j)
def Rinst.At (code : ByteArray) (pc : Nat) (r : Rinst) : Prop := code.getInst pc = some (.next (.reg r))
def Xinst.At (code : ByteArray) (pc : Nat) (x : Xinst) : Prop := code.getInst pc = some (.next (.exec x))

def Except.Split {ξ υ ζ : Type}
    (e : Except ξ υ) (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x) ∨ (∃ y : υ, e = .ok y ∧ q y)

def ExecuteCode (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  let evm : Evm := initEvm msg
  match msg.codeAddress with
  | .none =>
    ∃ ex', xl = .some ⟨evm, ex'⟩ ∧ executeCode.handleError ex' = ex
  | .some adr =>
    if adr.isPrecomp then
      (xl = .none ∧  executeCode.handleError (executePrecomp evm adr) = ex)
    else
      ∃ ex', xl = .some ⟨evm, ex'⟩ ∧ executeCode.handleError ex' = ex

def ProcessMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
    ( Except.assert (msg.depth ≤ 1024)
        ⟨ "StackDepthLimitError",
          msg.benv.state,
          msg.benv.createdAccounts,
          msg.tenv.transientStorage ⟩ ).Split ex <|
  λ _ =>
    msg.benvAfterTransfer.Split ex <|
  λ benv =>
  ∃ ex' : Except (String × State × AdrSet × Tra) Devm,
    And (ExecuteCode (msg.withBenv benv) xl ex') <|
    ex'.Split ex <|
  λ evm =>
    if evm.error.isSome then
      .ok (evm.rollback msg.benv.state msg.tenv.transientStorage) = ex
    else
      .ok evm = ex

def ProcessCreateMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  ∃ ex' : Except (String × State × AdrSet × Tra) Devm,
    And (ProcessMessage (processCreateMessage.msg msg) xl ex') <|
    ex'.Split ex <|
  λ evm =>
  if evm.error.isNone then
    match processCreateMessage.chargeCodeGas evm with
    | .ok evm => .ok (evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩) = ex
    | .error (err, evm) =>
      if isExceptionalHalt err then
        .ok
          ( processCreateMessage.exceptionalHalt evm err
              msg.benv.state
              msg.tenv.transientStorage ) = ex
      else
        .error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩ = ex
  else
    .ok (evm.rollback msg.benv.state msg.tenv.transientStorage) = ex

def ExistsEq {ξ} (t : ξ) (p : ξ → Prop) : Prop :=
  ∃ x : ξ, (x = t) ∧ p x

def GenericCreate (sevm : Sevm) (devm : Devm) (endowment : B256) (newAddress : Adr)
    (memoryIndex memorySize : Nat) (xl : Xlot) (ex : Execution) : Prop :=
    ExistsEq (devm.memory.data.sliceD memoryIndex memorySize 0) <|
  λ calldata =>
    ( Except.assert
        (memorySize ≤ maxInitcodeSize)
        ⟨"OutOfGasError", devm⟩ ).Split ex <|
  λ _ =>
    ExistsEq (addAccessedAddress devm newAddress) <|
  λ devm1 =>
    ExistsEq (except64th devm1.gasLeft) <|
  λ createMsgGas =>
    ExistsEq ({devm1 with gasLeft := devm1.gasLeft - createMsgGas}) <|
  λ devm2 =>
    (assertDynamic sevm devm2).Split ex <|
  λ _ =>
    ExistsEq ({devm2 with returnData := []}) <|
  λ devm3 =>
    ExistsEq (devm3.state.get sevm.currentTarget) <|
  λ sender =>
   if (sender.bal < endowment ∨ sender.nonce = B64.max ∨ sevm.depth + 1 > 1024) then
     ({devm3 with gasLeft := devm3.gasLeft + createMsgGas}.push 0 = ex)
   else
   ExistsEq (devm3.incrNonce sevm.currentTarget) <|
  λ devm4 =>
    if
      ( let target := devm4.state.get newAddress
        target.nonce ≠ (0 : B64) ∨ target.code.size ≠ 0 ∨ target.stor.size ≠ 0 ) then
      (devm4.push 0 = ex)
    else
    ExistsEq
      {
        benv := Benv.mk devm4.state devm4.createdAccounts sevm.benvStat
        tenv := {transientStorage := devm4.transientStorage, stat := sevm.tenvStat}
        caller := sevm.currentTarget
        target := .none
        gas := createMsgGas
        value := endowment
        data := []
        code := .mk <| .mk calldata
        currentTarget := newAddress
        depth := sevm.depth + 1
        codeAddress := .none
        shouldTransferValue := true
        isStatic := false
        accessedAddresses := devm4.accessedAddresses
        accessedStorageKeys := devm4.accessedStorageKeys
        disablePrecompiles := false
      } <|
  λ childMsg =>
  ∃ ex',
    And (ProcessCreateMessage childMsg xl ex') <|
    (liftToExecution devm4 ex').Split ex <|
  λ child =>
    if child.error.isSome then
      (incorporateChildOnError devm4 child child.output).push 0 = ex
    else
      (incorporateChildOnSuccess devm4 child []).push newAddress.toB256 = ex

def GenericCall
    (sevm: Sevm)
    (devm: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat)
    (code : ByteArray)
    (disablePrecompiles: Bool)
    (xl : Xlot)
    (ex : Execution) : Prop :=
    ExistsEq {devm with returnData := []} <|
  λ evm1 =>
    if (sevm.depth + 1 > 1024) then
      (({evm1 with gasLeft := evm1.gasLeft + gas}).push 0 = ex)
    else
    ExistsEq (evm1.memory.data.sliceD input_index input_size 0) <|
  λ calldata =>
    ExistsEq
      {
        benv := {state := evm1.state, createdAccounts := evm1.createdAccounts, stat := sevm.benvStat}
        tenv := {transientStorage := evm1.transientStorage, stat := sevm.tenvStat}
        caller := caller
        target := target
        gas := gas
        currentTarget := target
        value := value
        data := calldata
        codeAddress := codeAddress
        code := code
        depth := sevm.depth + 1
        shouldTransferValue := shouldTransferValue
        isStatic := isStaticcall || sevm.isStatic
        accessedAddresses := evm1.accessedAddresses
        accessedStorageKeys := evm1.accessedStorageKeys
        disablePrecompiles := disablePrecompiles
      } <|
    λ (childMsg : Msg) =>
    ∃ ex',
      And (ProcessMessage childMsg xl ex') <|
      (liftToExecution evm1 ex').Split ex <|
    λ child =>
      let actualOutput := child.output.take output_size
      if child.error.isSome then
        ((incorporateChildOnError evm1 child child.output).push 0).Split ex <|
      λ evm2 => .ok (evm2.memWrite output_index actualOutput) = ex
      else
        ((incorporateChildOnSuccess evm1 child child.output).push 1).Split ex <|
      λ evm2 => .ok (evm2.memWrite output_index actualOutput) = ex

def Xinst.Run (sevm : Sevm) (devm : Devm) :
    Xinst → Xlot → Execution → Prop
  | .create, xl, ex =>
      (devm.pop).Split ex <|
    λ ⟨endowment, devm1⟩ =>
      (devm1.popToNat).Split ex <|
    λ ⟨memoryIndex, devm2⟩ =>
      (devm2.popToNat).Split ex <|
    λ ⟨memorySize, devm3⟩ =>
      ExistsEq (devm3.extCost [⟨memoryIndex, memorySize⟩]) <|
    λ extendCost =>
      ExistsEq (gasInitCodeWordCost * (ceilDiv memorySize 32)) <|
    λ initCodeCost =>
      (chargeGas (gasCreate + extendCost + initCodeCost) devm3).Split ex <|
    λ devm4 =>
      ExistsEq (devm4.memExtends [⟨memoryIndex, memorySize⟩]) <|
    λ devm5 =>
      ExistsEq
        ( compute_contract_address
            sevm.currentTarget
            (devm5.state.get sevm.currentTarget).nonce ) <|
    λ newAddress =>
      GenericCreate
        sevm
        devm5
        endowment
        newAddress
        memoryIndex
        memorySize
        xl
        ex
  | .create2, xl, ex =>
      (devm.pop).Split ex <|
    λ ⟨endowment, devm1⟩ =>
      (devm1.popToNat).Split ex <|
    λ ⟨memoryIndex, devm2⟩ =>
      (devm2.popToNat).Split ex <|
    λ ⟨memorySize, devm3⟩ =>
      (devm3.pop).Split ex <|
    λ ⟨salt, devm4⟩ =>
      ExistsEq (devm4.extCost [⟨memoryIndex, memorySize⟩]) <|
    λ extendCost =>
      ExistsEq (gasKeccak256Word * ceilDiv memorySize 32) <|
    λ initCodeHashCost =>
      ExistsEq (gasInitCodeWordCost * (ceilDiv memorySize 32)) <|
    λ initCodeCost =>
      (chargeGas (gasCreate + initCodeHashCost + extendCost + initCodeCost) devm4).Split ex <|
    λ devm5 =>
      ExistsEq (devm5.memExtends [⟨memoryIndex, memorySize⟩]) <|
    λ devm6 =>
      ExistsEq
        ( create2NewAddress
            sevm.currentTarget
            salt
            (devm6.memory.data.sliceD memoryIndex memorySize 0) ) <|
    λ newAddress =>
      GenericCreate
        sevm
        devm6
        endowment
        newAddress
        memoryIndex
        memorySize
        xl
        ex
  | .call, xl, ex =>
      (devm.pop).Split ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).Split ex <|
    λ ⟨callee, devm2⟩ =>
      (devm2.pop).Split ex <|
    λ ⟨value, devm3⟩ =>
      (devm3.popToNat).Split ex <|
    λ ⟨inputIndex, devm4⟩ =>
      (devm4.popToNat).Split ex <|
    λ ⟨inputSize, devm5⟩ =>
      (devm5.popToNat).Split ex <|
    λ ⟨outputIndex, devm6⟩ =>
      (devm6.popToNat).Split ex <|
    λ ⟨outputSize, devm7⟩ =>
      ExistsEq (devm7.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ extendCost =>
      ExistsEq (access_cost callee devm7.accessedAddresses) <|
    λ preAccessCost =>
      ExistsEq (addAccessedAddress devm7 callee) <|
    λ devm8 =>
      ExistsEq (accessDelegation devm8 callee) <|
    λ ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm9⟩ =>
      ExistsEq (preAccessCost + delegatedAccessGasCost) <|
    λ accessCost =>
      ExistsEq (if (¬ (devm9.getAcct callee).Empty) ∨ value = 0 then 0 else gNewAccount) <|
    λ createCost =>
      ExistsEq (if value = 0 then 0 else gasCallValue) <|
    λ transferCost =>
      ExistsEq (calculateMsgCallGas value.toNat gas.toNat devm9.gasLeft extendCost (accessCost + createCost + transferCost)) <|
    λ ⟨msgCallCost, msgCallStipend⟩ =>
      (chargeGas (msgCallCost + extendCost) devm9).Split ex <|
    λ devm10 =>
      (Except.assert (!sevm.isStatic ∨ value = 0) ⟨"WriteInStaticContext", devm10⟩).Split ex <|
    λ _ =>
      ExistsEq (devm10.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ devm11 =>
      ExistsEq ((devm11.getAcct sevm.currentTarget).bal) <|
    λ senderBal =>
      if senderBal < value then
          (devm11.push 0).Split ex <|
        λ devm12 =>
          .ok {devm12 with returnData := [], gasLeft := devm12.gasLeft + msgCallStipend} = ex
      else
        GenericCall
          sevm
          devm11
          msgCallStipend
          value
          sevm.currentTarget
          callee
          callee
          true
          false
          inputIndex
          inputSize
          outputIndex
          outputSize
          code
          disablePrecompiles
          xl
          ex
  | .callcode, xl, ex =>
      (devm.pop).Split ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).Split ex <|
    λ ⟨codeAddress, devm2⟩ =>
      (devm2.pop).Split ex <|
    λ ⟨value, devm3⟩ =>
      (devm3.popToNat).Split ex <|
    λ ⟨inputIndex, devm4⟩ =>
      (devm4.popToNat).Split ex <|
    λ ⟨inputSize, devm5⟩ =>
      (devm5.popToNat).Split ex <|
    λ ⟨outputIndex, devm6⟩ =>
      (devm6.popToNat).Split ex <|
    λ ⟨outputSize, devm7⟩ =>
      ExistsEq (devm7.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ extendCost =>
      ExistsEq (access_cost codeAddress devm7.accessedAddresses) <|
    λ preAccessCost =>
      ExistsEq (addAccessedAddress devm7 codeAddress) <|
    λ devm8 =>
      ExistsEq (accessDelegation devm8 codeAddress) <|
    λ ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm9⟩ =>
      ExistsEq (preAccessCost + delegatedAccessGasCost) <|
    λ accessCost =>
      ExistsEq (if value = 0 then 0 else gasCallValue) <|
    λ transferCost =>
      ExistsEq (calculateMsgCallGas value.toNat gas.toNat devm9.gasLeft extendCost (accessCost + transferCost)) <|
    λ ⟨msgCallCost, msgCallStipend⟩ =>
      (chargeGas (msgCallCost + extendCost) devm9).Split ex <|
    λ devm10 =>
      ExistsEq (devm10.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ devm11 =>
      ExistsEq (devm11.getAcct sevm.currentTarget).bal <|
    λ senderBal =>
      if senderBal < value then
          (devm11.push 0).Split ex <|
        λ devm12 =>
          .ok {devm12 with returnData := [], gasLeft := devm12.gasLeft + msgCallStipend} = ex
      else
        GenericCall
          sevm
          devm11
          msgCallStipend
          value
          sevm.currentTarget
          sevm.currentTarget
          newCodeAddress
          true
          false
          inputIndex
          inputSize
          outputIndex
          outputSize
          code
          disablePrecompiles
          xl
          ex
  | .delcall, xl, ex =>
      (devm.pop).Split ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).Split ex <|
    λ ⟨codeAddress, devm2⟩ =>
      (devm2.popToNat).Split ex <|
    λ ⟨inputIndex, devm3⟩ =>
      (devm3.popToNat).Split ex <|
    λ ⟨inputSize, devm4⟩ =>
      (devm4.popToNat).Split ex <|
    λ ⟨outputIndex, devm5⟩ =>
      (devm5.popToNat).Split ex <|
    λ ⟨outputSize, devm6⟩ =>
      ExistsEq (devm6.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ extendCost =>
      ExistsEq (access_cost codeAddress devm6.accessedAddresses) <|
    λ preAccessCost =>
      ExistsEq (addAccessedAddress devm6 codeAddress) <|
    λ devm7 =>
      ExistsEq (accessDelegation devm7 codeAddress) <|
    λ ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm8⟩ =>
      ExistsEq (preAccessCost + delegatedAccessGasCost) <|
    λ accessCost =>
      ExistsEq (calculateMsgCallGas 0 gas.toNat devm8.gasLeft extendCost accessCost) <|
    λ ⟨msgCallCost, msgCallStipend⟩ =>
      (chargeGas (msgCallCost + extendCost) devm8).Split ex <|
    λ devm9 =>
      ExistsEq (devm9.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ devm10 =>
      GenericCall
        sevm
        devm10
        msgCallStipend
        sevm.value
        sevm.caller
        sevm.currentTarget
        newCodeAddress
        false
        false
        inputIndex
        inputSize
        outputIndex
        outputSize
        code
        disablePrecompiles
        xl
        ex
  | .statcall, xl, ex =>
      (devm.pop).Split ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).Split ex <|
    λ ⟨target, devm2⟩ =>
      (devm2.popToNat).Split ex <|
    λ ⟨inputIndex, devm3⟩ =>
      (devm3.popToNat).Split ex <|
    λ ⟨inputSize, devm4⟩ =>
      (devm4.popToNat).Split ex <|
    λ ⟨outputIndex, devm5⟩ =>
      (devm5.popToNat).Split ex <|
    λ ⟨outputSize, devm6⟩ =>
      ExistsEq (devm6.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ extendCost =>
      ExistsEq (access_cost target devm6.accessedAddresses) <|
    λ preAccessCost =>
      ExistsEq (addAccessedAddress devm6 target) <|
    λ devm7 =>
      ExistsEq (accessDelegation devm7 target) <|
    λ ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm8⟩ =>
      ExistsEq (preAccessCost + delegatedAccessGasCost) <|
    λ accessCost =>
      ExistsEq (calculateMsgCallGas 0 gas.toNat devm8.gasLeft extendCost accessCost) <|
    λ ⟨msgCallCost, msgCallStipend⟩ =>
      (chargeGas (msgCallCost + extendCost) devm8).Split ex <|
    λ devm9 =>
      ExistsEq (devm9.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ devm10 =>
      GenericCall
        sevm
        devm10
        msgCallStipend
        0
        sevm.currentTarget
        target
        target
        true
        true
        inputIndex
        inputSize
        outputIndex
        outputSize
        code
        disablePrecompiles
        xl
        ex

def Ninst.Run' (pc : Nat) (sevm : Sevm) (devm : Devm) :
    Ninst → Xlot → Execution → Prop
  | .push xs _, _, exn =>
    ( do let devm' ← chargeGas (if xs = [] then gBase else gVerylow) devm
         (devm'.push xs.toB256) ) = exn
  | .reg r, _, exn =>
    Rinst.run ⟨pc, sevm, devm⟩ r = exn
  | .exec x, xl, exn =>
    Xinst.Run sevm devm x xl exn

def Except.IsError {ξ υ : Type} (e : Except ξ υ) : Prop :=
  match e with
  | .error _ => True
  | .ok _ => False

/- Exec evm ex is provable iff
    ∃ lim : Nat, ∀ vb : bool, exec vb lim evm = ex
   holds, and ex is not a recursion limit error case.  -/
inductive Exec : Nat → Sevm → Devm → Execution → Type
  | invOp {pc} {sevm} {devm} :
    sevm.code.getInst pc = none →
    Exec pc sevm devm (.error ⟨"InvalidOpcode", devm⟩)
  | nextNoneErr {pc} {sevm} {devm} {n} {err} {devm'} :
    n.At sevm.code pc →
    Ninst.Run' pc sevm devm n .none (.error ⟨err, devm'⟩) →
    Exec pc sevm devm (.error ⟨err, devm'⟩)
  | nextSomeErr
    {pc} {sevm} {devm} {n} {pc_} {sevm_} {devm_} {exn_} {err} {devm'} :
    n.At sevm.code pc →
    Ninst.Run' pc sevm devm n
      (.some (⟨pc_, sevm_, devm_⟩, exn_))
      (.error ⟨err, devm'⟩) →
    Exec pc_ sevm_ devm_ exn_ →
    Exec pc sevm devm (.error ⟨err, devm'⟩)
  | nextNoneRec {pc} {sevm : Sevm} {devm} {n} {devm'} {exn} :
    n.At sevm.code pc →
    Ninst.Run' pc sevm devm n .none (.ok devm') →
    Exec (pc + n.size) sevm devm' exn →
    Exec pc sevm devm exn
  | nextSomeRec
    {pc} {sevm} {devm} {n} {pc_} {sevm_} {devm_}
    {exn_ : Execution} {devm'} {exn} :
    n.At sevm.code pc →
    Ninst.Run' pc sevm devm n
      (.some (⟨pc_, sevm_, devm_⟩, exn_))
      (.ok devm') →
    Exec pc_ sevm_ devm_ exn_ →
    Exec (pc + n.size) sevm devm' exn →
    Exec pc sevm devm exn
  | jumpErr {pc} {sevm} {devm} {j} {err} {devm'} :
    j.At sevm.code pc →
    Jinst.Run ⟨pc, sevm, devm⟩ j (.error ⟨err, devm'⟩) →
    Exec pc sevm devm (.error ⟨err, devm'⟩)
  | jumpRec {pc} {sevm} {devm} {j} {pc'} {devm'} {exn} :
    j.At sevm.code pc →
    Jinst.Run ⟨pc, sevm, devm⟩ j (.ok ⟨pc', devm'⟩) →
    Exec pc' sevm devm' exn →
    Exec pc sevm devm exn
  | last {pc} {sevm} {devm} {l} {exn} :
    l.At sevm.code pc →
    Linst.Run sevm devm l exn →
    Exec pc sevm devm exn

def Xlot.Filled : Xlot → Prop
  | .none => True
  | .some ⟨⟨pc, sevm, devm⟩, exn⟩ => Nonempty (Exec pc sevm devm exn)

def Ninst.Run (sevm : Sevm) (devm : Devm) (n : Ninst) (devm' : Devm) : Prop :=
  ∃ xl : Xlot, xl.Filled ∧
    ∃ pc, Ninst.Run' pc sevm devm n xl (.ok devm')

inductive Func.Run : List Func → Sevm → Devm → Func → Devm → Prop
  | zero :
    ∀ {fs sevm devm devm' f g devm''},
      Devm.PopBurn [0] devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | succ :
    ∀ {fs sevm devm w devm' f g devm_jd devm''},
      w ≠ 0 →
      Devm.PopBurn [w] devm devm' →
      Devm.Burn devm' devm_jd →
      Func.Run fs sevm devm_jd g devm'' →
      Func.Run fs sevm devm (branch f g) devm''
  | last :
    ∀ {fs sevm devm i devm' },
      Linst.Run sevm devm i (.ok devm') →
      Func.Run fs sevm devm (last i) devm'
  | next :
    ∀ {fs sevm devm i devm' f devm''},
      Ninst.Run sevm devm i devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (next i f) devm''
  | call :
    ∀ {fs sevm devm devm' k f devm''},
      fs[k]? = some f →
      Devm.Burn devm devm' →
      Func.Run fs sevm devm' f devm'' →
      Func.Run fs sevm devm (call k) devm''

def Prog.Run (sevm : Sevm) (devm : Devm) (p : Prog) (devm' : Devm) : Prop :=
  Func.Run (p.main :: p.aux) sevm devm p.main devm'

-------------------------------------------------------------------------------



def Except.toError? {ξ υ} : Except (String × ξ) υ → Option String
  | .ok _ => none
  | .error ⟨err, _⟩ => some err

def Except.Lim {ξ υ} (ex : Except (String × ξ) υ) : Prop :=
  ex.toError? = some "RecursionLimit"

def Except.Fit {ξ υ} (ex : Except (String × ξ) υ) : Prop := ¬ ex.Lim

def Xlot.Good' : Xlot → Prop
  | .none => True
  | .some (evm, ex) =>
    ex.Fit ∧ ∃ lim, exec false evm lim = ex

lemma of_lim_bind {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → Except (String × ξ) ζ} (h : (x >>= f).Lim) :
    x.Lim ∨ (∃ y, x = .ok y ∧ (f y).Lim) := by
  rcases x with ⟨err, s⟩ | y
  · left; simp [bind, Except.bind] at h; exact h
  · right; use y; constructor; rfl
    simp [bind, Except.bind] at h; exact h

lemma fit_push {evm : Devm} {x : B256} : ¬ (evm.push x).Lim := by
  unfold Except.Lim Devm.push Except.assert
  split
  · simp [Except.toError?, bind, Except.bind]
  · simp [Except.toError?, bind, Except.bind]

lemma fit_pop {evm : Devm} : ¬ evm.pop.Lim := by
  simp only [Except.Lim, Devm.pop, Except.toError?]
  cases evm.stack <;> simp

lemma fit_popToNat {evm : Devm} : ¬ evm.popToNat.Lim := by
  simp only [Except.Lim, Devm.popToNat, Except.toError?, Devm.pop]
  cases evm.stack <;> simp

lemma fit_pop_to_adr {evm : Devm} : ¬ evm.popToAdr.Lim := by
  simp only [Except.Lim, Devm.popToAdr, Except.toError?, Devm.pop]
  cases evm.stack <;> simp

lemma fit_chargeGas {cost : Nat} {evm : Devm} :
    ¬ (chargeGas cost evm).Lim := by
  simp only [Except.Lim, Except.toError?, chargeGas]
  cases safeSub evm.gasLeft cost <;> simp

lemma fit_assert {p ξ} [Decidable p]
    {s : String} {x : ξ} (ne : s ≠ "RecursionLimit") :
    ¬ (Except.assert p ⟨s, x⟩).Lim := by
  by_cases h : p <;>
    simp [h, Except.assert, Except.toError?, Except.Lim, ne]

lemma fit_assertDynamic {sevm : Sevm} {devm : Devm} :
    ¬ (assertDynamic sevm devm).Lim := fit_assert (by decide)

lemma fit_to_except {ξ υ} {x : ξ} {o : Option υ}
    {s : String} (ne : s ≠ "RecursionLimit") :
    ¬ (@Option.toExcept (String × ξ) υ ⟨s, x⟩ o).Lim := by
  simp only [Except.Lim, Except.toError?, Option.toExcept]
  cases o <;> simp [ne]

lemma fit_ok {ξ υ} {y : υ} :
    ¬ (.ok y : Except (String × ξ) υ).Lim := by intro h; cases h

lemma fit_pushItem {x : B256} {c : Nat} {evm : Devm} :
    ¬ (pushItem x c evm).Lim := by
  simp only [pushItem]; intro run
  rcases of_lim_bind run with run' | ⟨_, _, run'⟩
  · cases fit_chargeGas run'
  · cases fit_push run'

lemma fit_applyUnary {f : B256 → B256} {cost : Nat} {devm : Devm} :
    (applyUnary f cost devm).Fit := by
  simp only [applyUnary]; intro run
  rcases of_lim_bind run with run' | ⟨_, _, run'⟩
  · cases fit_pop run'
  · cases fit_pushItem run'

syntax "fit_bind_step " ident term : tactic
macro_rules
  | `(tactic| fit_bind_step $ltd $lem) => `(tactic|
      rcases of_lim_bind $ltd with ltd' | ⟨_, temp, ltd'⟩ <;>
      [
        (clear $ltd; apply $lem ltd' <;> clear ltd');
        (clear $ltd temp; rename' ltd' => $ltd)
      ]
    )

syntax "fit_bind_step' " ident term : tactic
macro_rules
  | `(tactic| fit_bind_step' $ltd $lem) => `(tactic|
      rcases of_lim_bind $ltd with ltd' | ⟨_, temp, ltd'⟩;
      swap; {apply $lem ltd'};
      clear $ltd; rename' ltd' => $ltd
    )

lemma fit_applyBinary {f : B256 → B256 → B256} {cost : Nat} {evm : Devm} :
    ¬ (applyBinary f cost evm).Lim := by
  simp only [applyBinary]; intro ltd
  fit_bind_step ltd fit_pop
  fit_bind_step ltd fit_pop
  cases fit_pushItem ltd

lemma fit_applyTernary {f : B256 → B256 → B256 → B256} {cost : Nat} {evm : Devm} :
    ¬ (applyTernary f cost evm).Lim := by
  simp only [applyTernary]; intro ltd
  fit_bind_step ltd fit_pop
  fit_bind_step ltd fit_pop
  fit_bind_step ltd fit_pop
  cases fit_pushItem ltd

lemma of_lim_map_rev {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → ζ} (ltd : (x <&> f).Lim) : x.Lim := by
  cases x <;> simp [Except.toError?, Except.Lim] at *; exact ltd

lemma fit_pop_n {evm : Devm} {n : Nat} : ¬ (evm.popN n).Lim := by
  induction n generalizing evm
  case zero =>
    simp [Devm.popN, Except.Lim, Except.toError?]
  case succ n ih =>
    simp only [Devm.popN]; intro ltd
    fit_bind_step ltd fit_pop
    fit_bind_step ltd ih; cases ltd

lemma Rinst.fit_run {evm : Evm} {r : Rinst} :
    (Rinst.run evm r).Fit := by
  intro ltd; cases r <;> simp only [Rinst.run, Rinst.runCore] at ltd
  case add => exact fit_applyBinary ltd
  case mul => exact fit_applyBinary ltd
  case sub => exact fit_applyBinary ltd
  case div => exact fit_applyBinary ltd
  case sdiv => exact fit_applyBinary ltd
  case mod => exact fit_applyBinary ltd
  case smod => exact fit_applyBinary ltd
  case addmod => exact fit_applyTernary ltd
  case mulmod => exact fit_applyTernary ltd
  case exp =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    exact fit_push ltd

  case signextend => exact fit_applyBinary ltd
  case lt => exact fit_applyBinary ltd
  case gt => exact fit_applyBinary ltd
  case slt => exact fit_applyBinary ltd
  case sgt => exact fit_applyBinary ltd
  case eq => exact fit_applyBinary ltd
  case iszero =>
    exact fit_applyUnary ltd
  case and => exact fit_applyBinary ltd
  case or => exact fit_applyBinary ltd
  case xor => exact fit_applyBinary ltd
  case not => exact fit_applyUnary ltd
  case byte => exact fit_applyBinary ltd
  case shr => exact fit_applyBinary ltd
  case shl => exact fit_applyBinary ltd
  case sar => exact fit_applyBinary ltd
  case kec =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    exact fit_push ltd
  case address => exact fit_pushItem ltd
  case balance =>
    fit_bind_step ltd fit_pop
    split at ltd <;>
    { fit_bind_step ltd fit_chargeGas;
      exact fit_push ltd }
  case origin => exact fit_pushItem ltd
  case caller => exact fit_pushItem ltd
  case callvalue => exact fit_pushItem ltd
  case calldataload =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    exact fit_push ltd
  case calldatasize => exact fit_pushItem ltd
  case calldatacopy =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    simp [Except.toError?, Except.Lim] at ltd
  case codesize => exact fit_pushItem ltd
  case codecopy =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    simp [Except.toError?, Except.Lim] at ltd
  case gasprice => exact fit_pushItem ltd
  case extcodesize =>
    fit_bind_step ltd fit_pop_to_adr
    split at ltd <;> fit_bind_step ltd fit_chargeGas
    · exact fit_push ltd
    · exact fit_push ltd
  case extcodecopy =>
    fit_bind_step ltd fit_pop_to_adr
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    split at ltd <;> fit_bind_step ltd fit_chargeGas
    · simp [Except.toError?, Except.Lim] at ltd
    · simp [Except.toError?, Except.Lim] at ltd
  case retdatasize => exact fit_pushItem ltd
  case retdatacopy =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    split at ltd <;> rename_i h_retdat
    · simp only [bind, Except.bind, Except.Lim, Except.toError?] at ltd;
      injection ltd; contradiction
    · simp [Except.toError?, Except.Lim] at ltd
  case extcodehash =>
    fit_bind_step ltd fit_pop_to_adr
    split at ltd <;> fit_bind_step ltd fit_chargeGas
    · exact fit_push ltd
    · exact fit_push ltd
  case blockhash =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    exact fit_push ltd
  case coinbase => exact fit_pushItem ltd
  case timestamp => exact fit_pushItem ltd
  case number => exact fit_pushItem ltd
  case prevrandao => exact fit_pushItem ltd
  case gaslimit => exact fit_pushItem ltd
  case chainid => exact fit_pushItem ltd
  case selfbalance => exact fit_pushItem ltd
  case basefee => exact fit_pushItem ltd
  case blobhash =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    exact fit_push ltd
  case blobbasefee => exact fit_pushItem ltd
  case pop =>
    fit_bind_step' ltd fit_chargeGas
    exact fit_pop <| of_lim_map_rev ltd
  case mload =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    exact fit_push ltd
  case mstore =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    simp [Except.toError?, Except.Lim] at ltd
  case mstore8 =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    simp [Except.toError?, Except.Lim] at ltd
  case sload =>
    fit_bind_step ltd fit_pop
    split at ltd <;> fit_bind_step ltd fit_chargeGas
    · exact fit_push ltd
    · exact fit_push ltd
  case sstore =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_pop
    have ne : "OutOfGasError" ≠ "RecursionLimit" := by decide
    fit_bind_step ltd (fit_assert ne)
    fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd fit_assertDynamic
    cases ltd
  case tload =>
    fit_bind_step ltd fit_pop
    exact fit_pushItem ltd
  case tstore =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd fit_assertDynamic
    cases ltd
  case mcopy =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    cases ltd
  case pc => exact fit_pushItem ltd
  case msize => exact fit_pushItem ltd
  case gas =>
    fit_bind_step ltd fit_chargeGas
    exact fit_push ltd
  case dup =>
    fit_bind_step ltd fit_chargeGas
    split at ltd
    · simp [Except.toError?, Except.Lim] at ltd
    · exact fit_push ltd
  case swap =>
    fit_bind_step ltd fit_chargeGas
    split at ltd
    · simp [Except.toError?, Except.Lim] at ltd
    · cases ltd
  case log =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_pop_n
    fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd fit_assertDynamic
    cases ltd

lemma Except.of_error_bind_eq {ξ υ ζ : Type}
    {x : ξ} {f : υ → Except ξ ζ} (e : Except ξ ζ)
    (eq : (Except.error x) >>= f = e) : Except.error x = e := by
  simp [bind, Except.bind] at eq; exact eq

lemma error_bind {ξ υ ζ : Type}
    {x : ξ} {f : υ → Except ξ ζ} :
    (Except.error x) >>= f = Except.error x := rfl

def ok_bind {ξ : Type u} {υ ζ : Type v} {y : υ} {g : υ → Except ξ ζ} :
    (.ok y) >>= g = g y := rfl

lemma fit_withPc {pc : ℕ} {exn : Execution} (fit : exn.Fit) :
    (exn.withPc pc).Fit := by
  simp only [Execution.withPc]
  rcases exn with ⟨err, devm⟩ | _
  · rw [error_bind]; exact fit
  · rw [ok_bind]; exact fit

lemma forall_gt_of_forall_gt_succ_pred {p : Nat → Prop} (n : Nat) :
    (∀ m > n, p (m.pred + 1)) → (∀ m > n, p m) := by
  intro fa m gt; rcases m with _ | m
  · cases Nat.not_lt_zero _ gt
  · apply fa (m + 1) gt

lemma fit_of_split_of_fit {ξ υ ζ} {x : Except (String × ξ) υ}
    {p : υ → Prop} {ex : Except (String × ξ) ζ}
    (split : Except.Split x ex p) (fit : x.Fit) :
    (∀ y, x = .ok y → p y → ex.Fit) → ex.Fit := by
  intro prem
  rcases split with ⟨⟨err, _⟩ , rw, rw'⟩ | ⟨y, eq, py⟩
  · rw [rw']; intro ltd; injection ltd with rw''
    rw [rw, rw''] at fit; cases fit rfl
  · exact (prem _ eq py)

syntax "fit_step_split " ident term : tactic
macro_rules
  | `(tactic| fit_step_split $run $lem) =>
    `(tactic|
      apply fit_of_split_of_fit $run $lem;
      clear $run; intro _ temp $run; clear temp;
    )

syntax "fit_step_exists " ident : tactic
macro_rules
  | `(tactic| fit_step_exists $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, temp, $run⟩; clear temp
    )

syntax "fit_step_exec " ident ident term:max term : tactic
macro_rules
  | `(tactic| fit_step_exec $run $good $lem $lem') =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨ex', runs, $run⟩;
      have temp := $lem $good runs; clear $good runs;
      rcases temp with ⟨fit, lim, run_eq⟩; clear lim run_eq;
      fit_step_split $run ($lem' fit); clear fit
    )

lemma fit_benvAfterTransfer {msg : Msg} : msg.benvAfterTransfer.Fit := by
  simp only [Msg.benvAfterTransfer]; intro ltd
  split at ltd
  · fit_bind_step ltd (fit_to_except (by decide)); exact fit_ok ltd
  · exact fit_ok ltd

lemma of_lim_handleError {ex : Execution} :
    (executeCode.handleError ex).Lim → ex.Lim := by
  rcases ex with ⟨err, err⟩ | _ <;>
    simp only [executeCode.handleError] <;> intro h
  · split at h; {cases h}; split at h; {cases h}; exact h
  · exact h

def Saturates {ξ υ} (n : Nat) (f : Nat → Except (String × ξ) υ) : Prop :=
  (f n).Fit → ∀ m, n < m → (f n = f m)

structure Saturation (lim : Nat) : Prop where
  (executeCode : ∀ (msg : Msg), Saturates lim (executeCode false msg))
  (processMessage : ∀ (msg : Msg), Saturates lim (processMessage false msg))
  ( processCreateMessage :
    ∀ (msg : Msg), Saturates lim (processCreateMessage false msg) )
  ( genericCreate :
    ∀ (sevm : Sevm) (devm : Devm)
      (endowment : B256) (newAddress : Adr)
      (memoryIndex : Nat) (memorySize : Nat),
      Saturates lim
        (genericCreate false sevm devm endowment newAddress memoryIndex memorySize) )
  ( genericCall :
    ∀ (sevm : Sevm) (devm : Devm)
      (gas : Nat) (value : B256) (caller : Adr) (target : Adr)
      (codeAddress : Adr) (shouldTransferValue : Bool) (isStaticcall : Bool)
      (inputIndex :Nat) (inputSize : Nat) (outputIndex : Nat)
      (outputSize : Nat) (code : ByteArray) (disablePrecompiles: Bool),
      Saturates lim
        ( genericCall false sevm devm gas value caller target codeAddress
            shouldTransferValue isStaticcall inputIndex inputSize outputIndex
            outputSize code disablePrecompiles ) )
  ( xinstRun :
    ∀ (sevm : Sevm) (devm : Devm) (x : Xinst),
      Saturates lim (Xinst.run false sevm devm x) )
  (ninstRun : ∀ (evm : Evm) (n : Ninst), Saturates lim (Ninst.run false evm n))
  (exec : ∀ (evm : Evm), Saturates lim (exec false evm))

lemma lim_handleError {ex : Execution} :
    ex.Lim → (executeCode.handleError ex).Lim := by
  intro h; rcases ex with ⟨err, err⟩ | _ <;>
    simp [Except.Lim, Except.toError?] at h
  rw [h]; rfl

lemma Except.bind_eq_bind {ξ υ ζ} {e : Except ξ υ} {f g : υ → Except ξ ζ}
    (eq : ∀ x, e = Except.ok x → f x = g x) : e >>= f = e >>= g := by
  cases e; rfl; apply eq _ rfl

lemma of_fit_bind {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → Except (String × ξ) ζ} (fit : (x >>= f).Fit) :
    x.Fit ∧ (∀ y, x = .ok y → (f y).Fit) := by
  constructor
  · intro ltd
    rcases x with ⟨_, _⟩ | _
    · injection ltd; rename_i rw; rw [rw] at fit; cases fit rfl
    · cases ltd
  · intro y eq; rw [eq] at fit; exact fit

syntax "eee_bind " ident  : tactic
macro_rules
  | `(tactic| eee_bind $fit) => `(tactic|
      apply Except.bind_eq_bind;
      intro _ eq_ok;
      have temp := $fit; clear $fit;
      have $fit :=
        @Eq.subst _ (Except.Fit) _ _ ok_bind <|
          @Eq.subst _ (λ e => Except.Fit (e >>= _)) _ _ eq_ok temp;
      clear temp eq_ok
    )

lemma of_fit_liftToExecution {evm : Devm}
    {f : Except (String × State × AdrSet × Tra) Devm} :
    (liftToExecution evm f).Fit → f.Fit := by
  rcases f with ⟨err, _⟩ | _ <;> intro fit ltd
  · injection ltd; rename_i rw; rw [rw] at fit; cases fit rfl
  · cases ltd

lemma saturation (lim : Nat) : Saturation lim := by
  induction lim
  case zero =>
    refine' ⟨_, _, _, _, _, _, _, _⟩
    · intro _ fit; simp only [executeCode] at fit; cases fit rfl
    · intro _ fit; simp only [processMessage] at fit; cases fit rfl
    · intro _ fit; simp only [processCreateMessage] at fit; cases fit rfl
    · intro _ _ _ _ _ _ fit; simp only [genericCreate] at fit; cases fit rfl
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fit;
      simp only [genericCall] at fit; cases fit rfl
    · intro _ _ x fit; cases x <;>
      {simp only [Xinst.run, Except.Fit] at fit; cases fit rfl}
    · intro _ n fit; cases n
      · simp only [Ninst.run, implies_true]
      · simp only [Ninst.run] at fit; cases fit rfl
      · simp only [Ninst.run, implies_true]
    · intro _ fit; simp only [exec] at fit; cases fit rfl
  case succ lim ih =>
    refine' ⟨_, _, _, _, _, _, _, _⟩
    · intro _ fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [executeCode] at *
      split at fit
      · rw [ih.exec _ (lim_handleError.mt fit) lim' (by omega)]
      · split at fit
        · rename_i pos; rw [if_pos pos, if_pos pos]
        · rename_i neg; rw [if_neg neg, if_neg neg]
          rw [ih.exec _ (lim_handleError.mt fit) lim' (by omega)]
    · intro _ fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [processMessage] at *
      eee_bind fit; eee_bind fit
      rw [ih.executeCode _ (of_fit_bind fit).1 lim' (by omega)]
    · intro _ fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [processCreateMessage] at *
      rw [ih.processMessage _ (of_fit_bind fit).1 lim' (by omega)]
    · intro _ _ _ _ _ _ fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [genericCreate] at *
      iterate 8 (eee_bind fit);
      split; {rfl}
      rename_i neg; rw [if_neg neg] at fit; clear neg
      eee_bind fit; eee_bind fit; split; {rfl}
      rename_i neg; rw [if_neg neg] at fit; clear neg
      eee_bind fit; eee_bind fit
      have fit' := of_fit_liftToExecution (of_fit_bind fit).1
      rw [ih.processCreateMessage _ fit' lim' (by omega)]
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [genericCall] at *
      eee_bind fit; split at fit
      · rename_i pos; rw [if_pos pos, if_pos pos]
      · rename_i neg; rw [if_neg neg, if_neg neg]
        iterate 3 (eee_bind fit)
        have fit' := of_fit_liftToExecution (of_fit_bind fit).1
        rw [ih.processMessage _ fit' lim' (by omega)]
    · intro _ _ x fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      rcases x  with _ | _ | _ | _ | _ | _ <;> simp only [Xinst.run] at *
      · iterate 8 (eee_bind fit)
        rw [ih.genericCreate _ _ _ _ _ _ fit lim' (by omega)]
      · iterate 19 (eee_bind fit)
        split; {rfl}; rename_i neg
        rw [if_neg neg] at fit; clear neg
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fit lim' (by omega)]
      · iterate 17 (eee_bind fit)
        split; {rfl}; rename_i neg
        rw [if_neg neg] at fit; clear neg
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fit lim' (by omega)]
      · iterate 14 (eee_bind fit)
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fit lim' (by omega)]
      · iterate 10 (eee_bind fit)
        rw [ih.genericCreate _ _ _ _ _ _ fit lim' (by omega)]
      · iterate 14 (eee_bind fit)
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ fit lim' (by omega)]
    · intro _ n fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      rcases n  with _ | _ | _ <;> simp only [Ninst.run] at *
      rw [ih.xinstRun _ _ _ fit lim' (by omega)]
    · intro _ fit lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [exec] at *; eee_bind fit; split
      · simp only at fit
        rw [← ih.ninstRun _ _ (of_fit_bind fit).1 lim' (by omega)]
        eee_bind fit; apply ih.exec _ fit lim' (by omega)
      · simp only at fit; eee_bind fit
        apply ih.exec _ fit lim' (by omega)
      · rfl

lemma fit_execute_ecrecover (evm : Evm) :
    (executeEcrecover evm).Fit := by
  intro ltd;
  fit_bind_step ltd fit_chargeGas
  fit_bind_step ltd fit_ok
  split at ltd
  · simp only [] at ltd
    split at ltd; {cases ltd}
    split at ltd <;> cases ltd
  · cases ltd

lemma fit_for_in {ξ υ} {xs : List Nat} {y : υ}
    {f : Nat → υ → Except (String × ξ) (ForInStep υ)}
    (fit : ∀ n y, (f n y).Fit) : (ForIn.forIn xs y f).Fit := by
  induction xs generalizing y with
    | nil => rw [List.forIn_nil]; intro ltd; cases ltd
    | cons x xs ih =>
      rw [List.forIn_cons]; intro ltd
      fit_bind_step ltd (fit _ _); split at ltd
      · cases ltd
      · apply ih ltd

lemma fit_catch_with_oog {ξ : Type U} {evm : Devm} {cond : String → Bool}
    {ex : Except String ξ} (fit : ex ≠ .error "RecursionLimit") :
    (catchWithOOG evm cond ex).Fit := by
  simp only [catchWithOOG]; split
  · apply fit_ok
  · split <;> intro ltd <;> injection ltd
    · contradiction
    . rename_i rw; rw [rw] at fit; cases fit rfl

lemma fit_toExStrBNP {xs} :
    B8L.toExStrBNP xs ≠ .error "RecursionLimit" := by
  simp only [B8L.toExStrBNP]; intro ltd
  split at ltd; {injection ltd; contradiction}
  split at ltd; {injection ltd; contradiction}
  split at ltd; {injection ltd; contradiction}
  simp [Option.toExcept] at ltd;
  split at ltd; {injection ltd; contradiction}
  cases ltd

lemma fit_toExStrBNP2 {xs} :
    B8L.toExStrBNP2 xs ≠ .error "RecursionLimit" := by
  simp only [B8L.toExStrBNP2]; intro ltd
  split at ltd; {injection ltd; contradiction}
  split at ltd; {injection ltd; contradiction}
  simp [Option.toExcept] at ltd;
  split at ltd; {injection ltd; contradiction}
  cases ltd

lemma fit_execute_precomp (evm : Evm) (adr : Adr) :
    (executePrecomp evm adr).Fit := by
  simp only [executePrecomp]; split
  · apply fit_execute_ecrecover
  · intro ltd; fit_bind_step ltd fit_chargeGas; cases ltd
  · intro ltd; fit_bind_step ltd fit_chargeGas; cases ltd
  · intro ltd; fit_bind_step ltd fit_chargeGas; cases ltd
  · intro ltd; fit_bind_step ltd fit_chargeGas
    split at ltd <;> cases ltd
  · intro ltd;
    fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd (fit_assert (by decide))
    fit_bind_step ltd (fit_to_except (by decide))
    fit_bind_step ltd (fit_to_except (by decide))
    cases ltd
  · intro ltd; fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd (fit_assert (by decide))
    fit_bind_step ltd (fit_to_except (by decide))
    cases ltd
  · intro ltd; fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd (fit_assert (by decide))
    fit_bind_step ltd (fit_for_in _)
    · intro n y ltd
      fit_bind_step ltd (fit_catch_with_oog fit_toExStrBNP)
      fit_bind_step ltd (fit_catch_with_oog fit_toExStrBNP2)
      fit_bind_step ltd (fit_assert (by decide))
      fit_bind_step ltd (fit_assert (by decide))
      fit_bind_step ltd (fit_to_except (by decide))
      cases ltd
    · cases ltd
  · intro ltd;
    fit_bind_step ltd (fit_assert (by decide))
    fit_bind_step ltd fit_chargeGas
    split at ltd
    · fit_bind_step ltd fit_ok
      fit_bind_step ltd (fit_to_except (by decide))
      cases ltd
    · fit_bind_step ltd fit_ok
      fit_bind_step ltd (fit_to_except (by decide))
      cases ltd
    · injection ltd; contradiction
  · intro ltd
    fit_bind_step ltd (fit_assert (by decide))
    injection ltd; contradiction
  · intro ltd
    fit_bind_step ltd (fit_assert (by decide))
    injection ltd; contradiction
  · intro ltd; simp only [executeBls12G1Msm] at ltd
    split at ltd
    · injection ltd; rename_i eq
      cases congr_arg String.head eq
    · simp only [pure_bind] at ltd
      fit_bind_step ltd fit_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12G2Add] at ltd
    split at ltd
    · injection ltd; contradiction
    · simp only [pure_bind] at ltd
      fit_bind_step ltd fit_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12G2Msm] at ltd
    split at ltd
    · injection ltd; rename_i eq
      cases congr_arg String.head eq
    · simp only [pure_bind] at ltd
      fit_bind_step ltd fit_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12Pairing] at ltd
    split at ltd
    · injection ltd; rename_i eq
      cases congr_arg String.head eq
    · simp only [pure_bind] at ltd
      fit_bind_step ltd fit_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12MapFpToG1] at ltd
    split at ltd
    · injection ltd; contradiction
    · simp only [pure_bind] at ltd
      fit_bind_step ltd fit_chargeGas
      injection ltd; contradiction
  · intro ltd; simp only [executeBls12MapFp2ToG2] at ltd
    fit_bind_step ltd (fit_assert (by decide))
    fit_bind_step ltd fit_chargeGas
    injection ltd; contradiction
  · intro ltd; injection ltd; rename_i eq
    cases congr_arg String.head eq

lemma of_execute_code' {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (good : xl.Good') (ec : ExecuteCode msg xl ex) :
    ex.Fit ∧ ∃ lim, ∀ lim' > lim, executeCode false msg lim' = ex := by
  simp only [ExecuteCode] at ec; split at ec
  · rename (msg.codeAddress = none) => eq_none
    rcases ec with ⟨ex', xl_eq, eq_ex⟩
    rw [xl_eq] at good
    simp [Xlot.Good'] at good
    rcases good with ⟨fit', lim, eq_ex'⟩
    have fit : ex.Fit := by
      rw [← eq_ex]
      exact (of_lim_handleError).mt fit'
    refine' ⟨fit, lim + 1, _⟩
    intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [executeCode]
    rw [eq_none]; simp only
    rw [← eq_ex'] at fit'
    rw [← (saturation lim).exec _ fit' lim' (by omega), eq_ex', eq_ex]
  · rename Adr => adr
    rename (msg.codeAddress = some adr) => eq_some
    split at ec
    · rename_i pos; constructor
      · rw [← ec.2]; intro ltd
        cases fit_execute_precomp _ _ <| of_lim_handleError ltd
      · refine' ⟨1, _⟩; intro lim' gt
        rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
        simp only [executeCode, eq_some, if_pos pos]; exact ec.2
    · rename_i neg; rcases ec with ⟨ex', xl_eq, eq_ex⟩
      rw [xl_eq] at good; simp [Xlot.Good'] at good
      rcases good with ⟨fit, lim, eq_ex'⟩
      constructor
      · rw [← eq_ex]; intro ltd;
        cases fit <| of_lim_handleError ltd
      · refine' ⟨lim + 1, _⟩; intro lim' gt
        rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
        simp only [executeCode]
        rw [eq_some]; simp only
        rw [if_neg neg]; rw [← eq_ex'] at fit
        rw [← (saturation lim).exec _ fit lim' (by omega), eq_ex', eq_ex]

lemma exists_forall_gt_ok_bind_eq {ξ υ ζ}
    {f : Nat → υ → Except (String × ξ) ζ} {y : υ} {ex : Except (String × ξ) ζ} :
    (∃ lim, ∀ lim' > lim, (f lim' y) = ex) →
    ∃ lim, ∀ lim' > lim, (.ok y >>= f lim') = ex := id

lemma exists_forall_gt_of_split {ξ υ ζ} {x : Except (String × ξ) υ}
    {ex : Except (String × ξ) ζ} {p : υ → Prop}
    {f : Nat → υ → Except (String × ξ) ζ} (split : Except.Split x ex p) :
    (∀ y, x = .ok y → p y → ∃ lim, ∀ lim' > lim, (f lim' y) = ex) →
    ∃ lim, ∀ lim' > lim, (x >>= f lim') = ex := by
  intro prem
  rcases split with ⟨⟨err, _⟩ , rw, rw'⟩ | ⟨y, eq, py⟩
  · refine' ⟨0, _⟩; intro _ _; rw [rw, rw']; rfl
  · rcases (prem _ eq py) with ⟨lim, fa⟩
    refine' ⟨lim, _⟩; intro lim' gt; rw [eq]; apply fa _ gt

syntax "efg_step_split " ident : tactic
macro_rules
  | `(tactic| efg_step_split $run) =>
    `(tactic|
      apply exists_forall_gt_of_split $run; clear $run;
      intro _ temp $run; clear temp
    )

lemma bind_eq_of_eq_ok_of_eq {ξ υ ζ} {x : Except ξ υ} {y} {z : Except ξ ζ}
    {f : υ → Except ξ ζ} (eq_ok : x = .ok y) (eq : f y = z) : (x >>= f) = z := by
  rw [eq_ok]; exact eq

syntax "eq_split " ident : tactic
macro_rules
  | `(tactic| eq_split $eq) => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨⟨_, _, _⟩, rw', rw⟩ | ⟨_, eq', $eq⟩ <;> [
        (rw [rw', rw]; rfl);
        (apply bind_eq_of_eq_ok_of_eq eq'; clear eq')
      ]
    )

lemma ite_eq_left_of_true {ξ : Sort u} {C : Prop} [h : Decidable C]
    {x y z : ξ} (c : C) (eq : x = z) : (if C then x else y) = z := by simp [c, eq]

lemma ite_eq_right_of_false {ξ : Sort u} {C : Prop} [h : Decidable C]
    {x y z : ξ} (c : ¬ C) (eq : y = z) : (if C then x else y) = z := by simp [c, eq]

lemma or_of_ite {c p q : Prop} [h : Decidable c] (h : if c then p else q) :
    (c ∧ p) ∨ (¬ c ∧ q) := by
  by_cases hc : c <;> simp [hc] at h
  · left; exact ⟨hc, h⟩
  · right; exact ⟨hc, h⟩

syntax "eq_ite " ident : tactic
macro_rules
  | `(tactic| eq_ite $eq) => `(tactic|
      rename' $eq => temp;
      rcases or_of_ite temp with ⟨pos, $eq⟩ | ⟨neg, $eq⟩ <;> clear temp <;>
      [
        (apply ite_eq_left_of_true pos; clear pos) ;
        (apply ite_eq_right_of_false neg; clear neg)
      ]
    )

lemma of_process_message' {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm} (good : xl.Good')
    (run : ProcessMessage msg xl ex) :
    ex.Fit ∧ ∃ lim, ∀ lim' > lim, processMessage false msg lim' = ex := by
  simp only [ProcessMessage] at run; constructor
  · fit_step_split run (fit_assert (by decide))
    fit_step_split run fit_benvAfterTransfer
    fit_step_exec run good of_execute_code' id
    split at run <;> (rw [← run]; apply fit_ok)
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [processMessage]
    efg_step_split run; efg_step_split run;
    have temp := run; clear run;
    rcases temp with ⟨ex', runs, run⟩;
    have temp := of_execute_code' good runs;
    clear good runs;
    rcases temp with ⟨fit, lim, run_eq⟩;
    clear fit;
    refine' ⟨lim + 1, _⟩;
    intro lim' gt;
    have gt' : lim'.pred > lim :=
    ( by cases lim' <;>
         [ (cases Nat.not_lt_zero _ gt);
           (exact Nat.lt_of_succ_lt_succ gt) ] );
    rw [run_eq lim'.pred gt'];
    clear gt gt' run_eq;
    eq_split run;
    eq_ite run <;> exact run

lemma processCreateMessage.fit_chargeCodeGas {evm : Devm} :
    (processCreateMessage.chargeCodeGas evm).Fit := by
  simp only [processCreateMessage.chargeCodeGas]; intro ltd
  split at ltd
  · injection ltd; contradiction
  · fit_bind_step ltd fit_chargeGas
    split at ltd
    · injection ltd; contradiction
    · cases ltd

syntax "efg_step_exec " ident ident term:max : tactic
macro_rules
  | `(tactic| efg_step_exec $run $good $lem) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨ex', runs, $run⟩;
      have temp := $lem $good runs;
      clear $good runs;
      rcases temp with ⟨fit, lim, run_eq⟩;
      clear fit;
      refine' ⟨lim + 1, _⟩;
      intro lim' gt;
      have gt' : lim'.pred > lim :=
      ( by cases lim' <;>
           [ (cases Nat.not_lt_zero _ gt);
             (exact Nat.lt_of_succ_lt_succ gt) ] );
      rw [run_eq lim'.pred gt'];
      clear gt gt' run_eq;
    )

syntax "efg_end_exec " ident ident term:max : tactic
macro_rules
  | `(tactic| efg_end_exec $run $good $lem) =>
    `(tactic|
      --have temp := $run; clear $run;
      --rcases temp with ⟨ex', runs, $run⟩;
      have temp := $lem $good $run; clear $good $run;
      rcases temp with ⟨fit, lim, run_eq⟩; clear fit;
      refine' ⟨lim + 1, _⟩;
      intro lim' gt;
      have gt' : lim'.pred > lim :=
      ( by cases lim' <;>
           [ (cases Nat.not_lt_zero _ gt);
             (exact Nat.lt_of_succ_lt_succ gt) ] );
      rw [run_eq lim'.pred gt']
    )


   -- rcases (of_generic_create' good run).2 with ⟨lim, fa⟩
   -- refine' ⟨lim + 1, λ lim' gt => _⟩
   -- have gt' : lim'.pred > lim :=
   --   ( by cases lim' <;>
   --        [ (cases Nat.not_lt_zero _ gt);
   --          (exact Nat.lt_of_succ_lt_succ gt) ] );
   -- rw [fa lim'.pred gt']


lemma of_process_create_message' {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm} (good : xl.Good')
    (run : ProcessCreateMessage msg xl ex) :
    ex.Fit ∧
      ∃ lim, ∀ lim' > lim, processCreateMessage false msg lim' = ex := by
  simp only [ProcessCreateMessage] at run; constructor
  · fit_step_exec run good of_process_message' id
    rename Devm => evm; split at run
    · split at run; {rw [← run]; apply fit_ok}
      rename_i eq; split at run
      · rw [← run]; apply fit_ok
      · rw [← run]; intro ltd; injection ltd with rw
        have fit := @processCreateMessage.fit_chargeCodeGas evm
        rw [eq, rw] at fit; cases fit rfl
    · rw [← run]; apply fit_ok
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [processCreateMessage]
    efg_step_exec run good of_process_message'
    eq_split run; eq_ite run
    · split at run <;> rename_i rw <;> rw [rw]
      · exact run
      · eq_ite run <;> exact run
    · exact run

syntax "efg_step_exists " ident : tactic
macro_rules
  | `(tactic| efg_step_exists $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨_, rw, $run⟩;
      rw [← rw]; clear rw;
      apply exists_forall_gt_ok_bind_eq
    )

lemma exists_forall_gt_imp {p q : Nat → Prop} :
    (∀ n, p n → q n) → (∃ n, ∀ m > n, p m) → (∃ n, ∀ m > n, q m) := by
  intro imp ⟨n, fa⟩; refine ⟨n, λ m gt => imp m (fa m gt)⟩

lemma fit_liftToExecution {evm : Devm}
    {f : Except (String × State × AdrSet × Tra) Devm}
    (fit : f.Fit) : (liftToExecution evm f).Fit := by
  cases f
  · exact fit
  · simp only [liftToExecution]; intro ltd; cases ltd

lemma ok_bind' {ξ υ ζ} {y : υ}
    {f : υ → Except ξ ζ} {z : Except ξ ζ}
    (eq : f y = z) : (.ok y >>= f) = z := by
  rw [ok_bind]; exact eq

syntax "efg_step_early " ident : tactic
macro_rules
  | `(tactic| efg_step_early $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases or_of_ite temp with ⟨pos, $run⟩ | ⟨neg, $run⟩ <;> clear temp <;> [
        ( apply exists_forall_gt_imp (λ _ => ite_eq_left_of_true pos);
          simp only [bind_pure]; clear pos );
        ( apply exists_forall_gt_imp (λ _ => ite_eq_right_of_false neg ∘ ok_bind');
          clear neg )
      ]
    )

lemma of_generic_create' {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : ℕ} {xl : Xlot} {ex : Execution} (good : xl.Good')
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl ex) :
    ex.Fit ∧
      ∃ lim,
        ∀ lim' > lim,
          genericCreate false sevm devm endowment
            newAddress memoryIndex memorySize lim' = ex := by
  simp only [GenericCreate] at run; constructor
  · fit_step_exists run
    fit_step_split run (fit_assert (by decide))
    iterate 3 (fit_step_exists run);
    fit_step_split run fit_assertDynamic
    iterate 2 (fit_step_exists run);
    split at run; {rw [← run]; apply fit_push}
    fit_step_exists run
    split at run; {rw [← run]; apply fit_push}
    fit_step_exists run
    fit_step_exec run good of_process_create_message' fit_liftToExecution
    split at run <;> (rw [← run]; apply fit_push)
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [genericCreate]
    efg_step_exists run; efg_step_split run
    iterate 3 (efg_step_exists run)
    efg_step_split run; iterate 2 (efg_step_exists run)
    efg_step_early run; {refine' ⟨0, _⟩; intro _ _; exact run}
    efg_step_exists run
    efg_step_early run; {refine' ⟨0, _⟩; intro _ _; exact run}
    efg_step_exists run
    efg_step_exec run good of_process_create_message'
    eq_split run; eq_ite run <;> exact run

lemma fit_map_rev {ξ υ ζ} {x : Except (String × ξ) υ}
    {f : υ → ζ} : x.Fit → (x <&> f).Fit  := of_lim_map_rev.mt

lemma of_generic_call' {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {ex : Execution} (good : xl.Good')
    ( run :
      GenericCall sevm devm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles xl ex ) :
    ex.Fit ∧
      ∃ lim, ∀ lim' > lim,
        genericCall false sevm devm gas value caller target codeAddress
          shouldTransferValue isStaticcall input_index input_size
          output_index output_size code disablePrecompiles lim' = ex := by
  simp only [GenericCall] at run; constructor
  · fit_step_exists run
    split at run; {rw [← run]; apply fit_push}
    fit_step_exists run
    fit_step_exists run
    fit_step_exec run good of_process_message' fit_liftToExecution
    split at run <;>
    {fit_step_split run fit_push; rw [← run]; apply fit_ok}
  · apply Exists.imp forall_gt_of_forall_gt_succ_pred
    simp only [genericCall]; efg_step_exists run;
    efg_step_early run; {refine' ⟨0, _⟩; intro _ _; exact run}
    efg_step_exists run; efg_step_exists run;
    efg_step_exec run good of_process_message'; eq_split run
    eq_ite run <;> {eq_split run; exact run}

syntax "efg_step_ite " ident : tactic
macro_rules
  | `(tactic| efg_step_ite $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases or_of_ite temp with ⟨pos, $run⟩ | ⟨neg, $run⟩ <;> clear temp <;> [
        ( apply exists_forall_gt_imp (λ _ => ite_eq_left_of_true pos);

          clear pos );
        ( apply exists_forall_gt_imp (λ _ => ite_eq_right_of_false neg);
          clear neg )
      ]
    )

lemma Xinst.run_eq_of_run {sevm} {devm} {x : Xinst} {xl : Xlot}
    {ex} (good : xl.Good') (run : Xinst.Run sevm devm x xl ex) :
    ex.Fit ∧ ∃ lim, ∀ lim' > lim, Xinst.run false sevm devm x lim' = ex := by
  cases x <;>
    ( constructor <;>
      [ skip;
        ( apply Exists.imp forall_gt_of_forall_gt_succ_pred ;
          simp only [Xinst.run] ) ] )
  · fit_step_split run fit_pop
    fit_step_split run fit_popToNat
    fit_step_split run fit_popToNat
    fit_step_exists run; fit_step_exists run
    fit_step_split run fit_chargeGas
    fit_step_exists run; fit_step_exists run
    exact (of_generic_create' good run).1
  · iterate 3 (efg_step_split run)
    iterate 2 (efg_step_exists run)
    efg_step_split run
    iterate 2 (efg_step_exists run)
    efg_end_exec run good of_generic_create'
  · fit_step_split run fit_pop
    fit_step_split run (fit_map_rev fit_pop)
    fit_step_split run fit_pop
    iterate 4 (fit_step_split run fit_popToNat)
    iterate 3 (fit_step_exists run)
    fit_step_exists run
    iterate 3 (fit_step_exists run)
    fit_step_exists run
    fit_step_split run fit_chargeGas
    fit_step_split run (fit_assert (by decide))
    fit_step_exists run; fit_step_exists run
    split at run
    · fit_step_split run fit_push
      rw [← run]; apply fit_ok
    · exact (of_generic_call' good run).1
  · iterate 7 (efg_step_split run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    efg_step_split run; efg_step_split run;
    efg_step_exists run; efg_step_exists run;
    efg_step_ite run
    · efg_step_split run; refine ⟨0, λ _ _ => run⟩
    · efg_end_exec run good of_generic_call'
  · fit_step_split run fit_pop
    fit_step_split run (fit_map_rev fit_pop)
    fit_step_split run fit_pop
    iterate 4 (fit_step_split run fit_popToNat)
    iterate 4 (fit_step_exists run)
    fit_step_exists run
    fit_step_exists run; fit_step_exists run
    fit_step_split run fit_chargeGas
    fit_step_exists run; fit_step_exists run
    split at run
    · fit_step_split run fit_push
      rw [← run]; apply fit_ok
    · exact (of_generic_call' good run).1
  · iterate 7 (efg_step_split run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    iterate 2 (efg_step_exists run)
    efg_step_exists run;
    efg_step_split run
    iterate 2 (efg_step_exists run)
    efg_step_ite run
    · efg_step_split run; refine ⟨0, λ _ _ => run⟩
    · efg_end_exec run good of_generic_call'
  · fit_step_split run fit_pop
    fit_step_split run (fit_map_rev fit_pop)
    iterate 4 (fit_step_split run fit_popToNat)
    iterate 3 (fit_step_exists run)
    fit_step_exists run
    fit_step_exists run
    fit_step_exists run
    fit_step_split run fit_chargeGas
    fit_step_exists run;
    exact (of_generic_call' good run).1
  · iterate 6 (efg_step_split run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    efg_step_exists run
    efg_step_exists run;
    efg_step_split run
    efg_step_exists run
    efg_end_exec run good of_generic_call'
  · fit_step_split run fit_pop
    iterate 2 (fit_step_split run fit_popToNat)
    fit_step_split run fit_pop
    iterate 3 (fit_step_exists run)
    fit_step_split run fit_chargeGas
    iterate 2 (fit_step_exists run)
    exact (of_generic_create' good run).1
  · iterate 4 (efg_step_split run)
    iterate 3 (efg_step_exists run)
    efg_step_split run
    iterate 2 (efg_step_exists run)
    efg_end_exec run good of_generic_create'
  · fit_step_split run fit_pop
    fit_step_split run (fit_map_rev fit_pop)
    iterate 4 (fit_step_split run fit_popToNat)
    iterate 3 (fit_step_exists run)
    fit_step_exists run
    fit_step_exists run
    fit_step_exists run
    fit_step_split run fit_chargeGas
    fit_step_exists run;
    exact (of_generic_call' good run).1
  · iterate 6 (efg_step_split run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    efg_step_exists run
    efg_step_exists run;
    efg_step_split run
    efg_step_exists run
    efg_end_exec run good of_generic_call'

lemma cast_fit {ξ υ ζ} {erx : String × ξ}
    (fit : (.error erx : Except (String × ξ) υ).Fit) :
    (.error erx : Except (String × ξ) ζ).Fit := by
  simp only [Except.Fit] at *; apply mt _ fit
  simp only [Except.toError?, Except.Lim] at *
  simp only [fit, imp_self]

lemma Ninst.run_of_run' {pc} {sevm} {devm} {n : Ninst} (xl : Xlot)
    {ex} (good : xl.Good') (run : Ninst.Run' pc sevm devm n xl ex) :
    ex.Fit ∧ ∃ lim, ∀ lim' > lim, Ninst.run false ⟨pc, sevm, devm⟩ n lim' = ex := by
  rcases n with r | x | ⟨xs, le⟩
  · simp only [Ninst.Run'] at run
    simp only [Ninst.run]; constructor;
    · rw [← run]; apply Rinst.fit_run
    · refine ⟨0, λ _ _ => run⟩;
  · simp only [Ninst.Run'] at run; constructor
    · exact (Xinst.run_eq_of_run good run).1
    · rcases Xinst.run_eq_of_run good run with ⟨fit, lim, run_eq⟩;
      refine' ⟨lim + 1, λ lim' gt => _⟩
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
      simp only [Ninst.run];
      apply run_eq lim' (by omega)
  · simp [Ninst.Run'] at run; constructor
    · rw [← run]; intro ltd
      fit_bind_step ltd fit_chargeGas
      exact fit_push ltd
    · simp only [Ninst.run]; refine' ⟨0, λ _ _ => run⟩

lemma Except.bind_eq_of_is_error {ξ υ : Type} {e : Except ξ υ}
    {f : υ → Except ξ υ} : e.IsError → (e >>= f) = e := by
  intro h; cases e
  · rfl
  · cases h

lemma Jinst.fit_run {evm} {j : Jinst} : (Jinst.run evm j).Fit := by
  intro ltd; cases j <;> simp only [Jinst.run] at ltd
  case jumpi =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    split at ltd
    · fit_bind_step ltd fit_ok; cases ltd
    · fit_bind_step ltd (fit_assert (by decide))
      fit_bind_step ltd fit_ok; cases ltd
  case jumpdest =>
    fit_bind_step ltd fit_chargeGas; cases ltd
  case jump =>
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd (fit_assert (by decide))
    cases ltd

lemma Linst.fit_run {sevm} {devm} {l : Linst} : (Linst.run sevm devm l).Fit := by
  intro ltd; cases l
  case stop => cases ltd
  case rev =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    simp [Except.Lim, Except.toError?] at ltd
  case ret =>
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_popToNat
    fit_bind_step ltd fit_chargeGas
    simp [Except.Lim, Except.toError?] at ltd
  case dest =>
    simp only [Devm.popToAdr, bind_map_left, Linst.run] at ltd
    fit_bind_step ltd fit_pop
    fit_bind_step ltd fit_chargeGas
    fit_bind_step ltd fit_assertDynamic
    have ne : "ERROR : InsufficientBalanceError" ≠ "RecursionLimit" := by decide
    fit_bind_step ltd (fit_to_except ne)
    split at ltd <;> simp [Except.Lim, Except.toError?] at ltd

lemma of_exec' :
    ∀ (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      Exec pc sevm devm exn →
      exn.Fit ∧
        ∃ lim, ∀ lim' > lim, (exec false ⟨pc, sevm, devm⟩ lim' = exn) := by
  apply Exec.rec
  · intro pc sevm devm eq; refine' ⟨_, 0, _⟩
    · intro ltd; injection ltd; contradiction
    · intro lim' gt; cases lim'; {cases Nat.not_lt_zero _ gt}
      simp only [exec, Option.toExcept, Evm.getInst, eq]; rfl
  · intro pc sevm devm n err devm' nat run
    rcases Ninst.run_of_run' .none .intro run with ⟨fit, lim, eq⟩
    refine' ⟨fit, lim + 2, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, exec, Option.toExcept, nat, ok_bind]
    rw [eq lim' (by omega)]; rfl
  · intro pc sevm devm n pc_ sevm_ devm_ exn_ exn devm' nat run exc ⟨fit_, limExec, exec_eq⟩
    rcases
      Ninst.run_of_run'
        (.some ⟨⟨pc_, sevm_, devm_⟩, exn_⟩)
        ⟨fit_, limExec + 1, exec_eq _ (by omega)⟩
        run
      with ⟨fit, limRun, run_eq⟩
    refine' ⟨fit, (max limExec limRun) + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, ok_bind, exec, Option.toExcept, nat]
    rw [run_eq lim' (by omega)]; rfl
  · intro pc sevm devm n devm' exn nat run exc ⟨fit, limExec, exec_eq⟩
    rcases Ninst.run_of_run' .none .intro run
      with ⟨temp, limRun, run_eq⟩; clear temp
    refine' ⟨fit, (max limExec limRun) + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, ok_bind, exec, Option.toExcept, nat]
    rw [run_eq lim' (by omega)]; apply exec_eq _ (by omega)
  · intro pc sevm devm n pc_ sevm_ devm_ exn_ devm' exn nat run exc_ exc
      ⟨fit_, limExec_, eq_⟩
      ⟨fit, limExec, eq⟩
    rcases
      Ninst.run_of_run'
        (.some ⟨⟨pc_, sevm_, devm_⟩, exn_⟩)
        ⟨fit_, limExec_ + 1, eq_ _ (by omega)⟩
        run
      with ⟨fitRun, limRun, run_eq⟩
    refine' ⟨fit, max limRun limExec + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, ok_bind, _root_.exec, Option.toExcept, nat]
    rw [run_eq lim' (by omega)]
    apply eq _ (by omega)
  · intro pc sevm devm j err devm' nat run
    simp only [Jinst.At] at nat
    simp only [Jinst.Run] at run
    constructor
    · have fit := @Jinst.fit_run ⟨pc, sevm, devm⟩ j
      rw [run] at fit; exact fit
    · refine' ⟨0, _⟩; intro lim gt
      rcases lim with _ | lim; {cases Nat.not_lt_zero _ gt}
      simp only [Evm.getInst, exec, nat, Option.toExcept, ok_bind, run]; rfl
  · intro pc sevm devm j pc' devm' exn jat run exc ⟨fit, lim, exec_eq⟩
    simp only [Jinst.At] at jat
    simp only [Jinst.Run] at run
    refine' ⟨fit, lim + 1, _⟩; intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Evm.getInst, exec, jat, Option.toExcept, ok_bind, run]
    apply exec_eq _ (by omega)
  · intro pc sevm devm l exn lat run
    simp only [Linst.At] at lat
    simp only [Linst.Run] at run
    have fit := @Linst.fit_run sevm devm l; rw [run] at fit
    refine' ⟨fit, 0, _⟩; intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Evm.getInst, exec, lat, Option.toExcept, ok_bind, run]

--def Except.Fit {ξ υ} (ex : Except (String × ξ) υ) : Prop := ¬ ex.Lim
def Xlot.Good {ξ υ} (lim : Nat) (ex : Except (String × ξ) υ) : Xlot → Prop
  | .none => True
  | .some (evm, exn) =>
    ∃ lim' < lim, exec false evm lim' = exn ∧ (exn.Lim → ex.Lim)

syntax "bind_step_good " ident rcasesPat : tactic
macro_rules
  | `(tactic| bind_step_good $h $pat) => `(tactic|
      rcases of_bind_eq $h with im | ⟨$pat, temp_eq, eq'⟩;
      { refine ⟨.none, .intro, .inl im⟩ };
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, Or.inr ⟨_, temp_eq, conj.2⟩⟩);
      clear temp_eq
    )

syntax "okStep1 " ident rcasesPat : tactic
macro_rules
  | `(tactic| okStep1 $h $pat1) => `(tactic|
      rcases of_bind_eq $h with ⟨_, ⟨_⟩, _⟩ | ⟨$pat1, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, ⟨_, (Except.ok.inj temp_eq).symm, conj.2⟩⟩);
      clear temp_eq
    )

syntax "okStep2 " ident rcasesPat rcasesPat : tactic
macro_rules
  | `(tactic| okStep2 $h $pat1 $pat2) => `(tactic|
      rcases of_bind_eq $h with ⟨_, ⟨_⟩, _⟩ | ⟨⟨$pat1, $pat2⟩, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, ⟨_, (Except.ok.inj temp_eq).symm, conj.2⟩⟩);
      clear temp_eq
    )

syntax "okStep5 " ident rcasesPat rcasesPat rcasesPat rcasesPat rcasesPat : tactic
macro_rules
  | `(tactic| okStep5 $h $pat1 $pat2 $pat3 $pat4 $pat5) => `(tactic|
      rcases of_bind_eq $h
        with ⟨_, ⟨_⟩, _⟩ | ⟨⟨$pat1, $pat2, $pat3, $pat4, $pat5⟩, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, ⟨_, (Except.ok.inj temp_eq).symm, conj.2⟩⟩);
      clear temp_eq
    )

syntax "bind_step' " ident rcasesPat : tactic
macro_rules
  | `(tactic| bind_step' $h $pat) => `(tactic|
      rcases of_bind_eq $h with im | ⟨$pat, temp_eq, eq'⟩;
      {left; exact im}; clear $h; rename' eq' => $h;
      right; refine' ⟨_, temp_eq, _⟩; clear temp_eq
    )

lemma Except.fit_of_fit {ξ} {υ} {ζ}
    {f : Except (String × ξ) υ}
    {g : υ → Except (String × ξ) ζ}
    {ex : Except (String × ξ) ζ}
    (notLimited : ex.Fit) (eq : f >>= g = ex) : f.Fit := by
  intro rw; rcases f with ⟨_, _⟩ | _ <;>
    simp [Except.Lim, Except.toError?] at rw
  rw [rw] at eq; rw [← eq] at notLimited; cases notLimited rfl

lemma Execution.fit_of_fit {ξ} {υ}
    {f : Except (String × Devm) ξ}
    {g : ξ → Except (String × Devm) υ}
    {ex : Except (String × Devm) υ}
    (fit : ex.Fit) (eq : f >>= g = ex) : f.Fit := by
  intro rw; rcases f with ⟨evm, err⟩ | _ <;>
    simp [Except.Lim, Except.toError?] at rw
  rw [rw] at eq; rw [← eq] at fit; cases fit rfl

lemma ite_of_true {c : Prop} [Decidable c] {p q : Prop} :
    c → p → if c then p else q := by
  intro hc hp; rw [if_pos hc]; exact hp

lemma ite_of_false {c : Prop} [Decidable c] {p q : Prop} :
    ¬ c → q → if c then p else q := by
  intro hc hp; rw [if_neg hc]; exact hp

lemma Except.of_toError?_eq_some {ξ} {υ} (ex : Except (String × ξ) υ)
    (err : String) (eq : ex.toError? = some err) :
    ∃ x, ex = .error ⟨err, x⟩ := by
  rcases ex with ⟨err', _⟩ | _ <;> simp [Except.toError?] at eq
  cases eq; refine ⟨_, rfl⟩

lemma of_executeCode {msg : Msg} {lim : Nat}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (notLimited : ex.Fit)
    (eq : executeCode false msg lim = ex) :
    ∃ xl : Xlot, xl.Good lim ex ∧ ExecuteCode msg xl ex := by
  rcases lim with _ | lim <;> simp only [executeCode] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  split at eq
  · rename msg.codeAddress = .none => eq_none
    refine'
      ⟨ .some ⟨initEvm msg, exec false (initEvm msg) lim⟩,
        ⟨lim, (by omega), rfl, λ halts => _⟩, _ ⟩
    · rcases Except.of_toError?_eq_some _ _ halts with ⟨evm, rw⟩
      rw [← eq, rw] at notLimited; cases notLimited rfl
    · simp only [ExecuteCode]; rw [eq_none]; refine' ⟨_, rfl, eq⟩
  · rename Adr => adr
    rename msg.codeAddress = .some adr => eq_some
    split at eq
    · rename_i pos; refine' ⟨.none, .intro, _⟩
      simp only [ExecuteCode]; rw [eq_some]
      simp only []; rw [if_pos pos]; simp [eq]
    · rename_i neg
      refine'
        ⟨ .some ⟨initEvm msg, exec false (initEvm msg) lim⟩,
          ⟨lim, (by omega), rfl, λ halts => _⟩, _ ⟩
      · rcases Except.of_toError?_eq_some _ _ halts with ⟨evm, rw⟩
        rw [← eq, rw] at notLimited; cases notLimited rfl
      · simp only [ExecuteCode]; rw [eq_some]
        simp only []; rw [if_neg neg]; refine' ⟨_, rfl, eq⟩

lemma good_of_good_of_fit
    {ξ υ ζ ω}
    {lim lim' : Nat}
    {oe  : Except (String × ξ) υ}
    {oe' : Except (String × ζ) ω}
    {xl : Xlot} (le : lim ≤ lim') (ne : oe.Fit)
    (good : xl.Good lim oe) : xl.Good lim' oe' := by
  rcases xl with _ | ⟨evm, ex⟩; {constructor}
  rcases good with ⟨_, lt, exec, of_eq⟩

  refine' ⟨_, Nat.lt_of_lt_of_le lt le, exec,  _⟩
  intro eq; cases ne <| of_eq eq

lemma of_processMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (notLimited : ex.Fit)
    (eq : processMessage false msg lim = ex) :
    ∃ xl : Xlot, xl.Good lim ex ∧ ProcessMessage msg xl ex := by
  rcases lim with _ | lim <;> simp only [processMessage] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  bind_step_good eq _; bind_step_good eq _
  have notLimited' := Except.fit_of_fit notLimited eq
  rcases of_executeCode notLimited' rfl with ⟨xl, good, ec⟩
  refine' ⟨_, good_of_good_of_fit (by omega) notLimited' good, _, ec, _⟩
  bind_step' eq _; split at eq
  · rename_i pos; rw [if_pos pos]; exact eq
  · rename_i neg; rw [if_neg neg]; exact eq

lemma of_processCreateMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (notLimited : ex.Fit)
    (eq : processCreateMessage false msg lim = ex) :
    ∃ xl : Xlot,
      xl.Good lim ex ∧
      ProcessCreateMessage msg xl ex := by
  rcases lim with _ | lim <;> simp only [processCreateMessage] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  have notLimited' :
    (processMessage false (processCreateMessage.msg msg) lim).Fit := by
    intro pm_eq
    rcases Except.of_toError?_eq_some _ _ pm_eq with ⟨_, rw⟩
    rw [← eq, rw] at notLimited
    cases notLimited rfl
  rcases @of_processMessage _ _ _ notLimited' rfl
    with ⟨xl, good, pcm⟩
  refine' ⟨_, good_of_good_of_fit (by omega) notLimited' good, _, pcm, _⟩
  bind_step' eq evm'
  split at eq
  · rename_i pos; rw [if_pos pos]
    cases pcm_eq : processCreateMessage.chargeCodeGas evm'
    · simp only []
      rw [pcm_eq] at eq
      simp only [] at eq
      split at eq
      · rename_i pos; rw [if_pos pos]; exact eq
      · rename_i neg; rw [if_neg neg]; exact eq
    · rw [pcm_eq] at eq; exact eq
  · rename_i neg; rw [if_neg neg]; exact eq

lemma of_genericCreate
    {sevm : Sevm} {devm : Devm} {endow : B256} {newAdr : Adr}
    {memIndex memSize lim : ℕ} {ex : Execution}
    (notLimited : ex.Fit)
    (eq : genericCreate false sevm devm endow newAdr memIndex memSize lim = ex) :
    ∃ xl : Xlot,
      xl.Good lim ex ∧
      GenericCreate sevm devm endow newAdr memIndex memSize xl ex := by
  rcases lim with _ | lim <;> simp only [genericCreate] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _
  okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _
  split at eq
  · rename_i pos
    apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_true pos conj.2⟩)
    rcases of_bind_eq eq with ⟨es, push_eq, ex_eq⟩ | ⟨evm, push_eq, eq_ex⟩;
    · refine' ⟨.none, .intro, _⟩; rw [ex_eq]; exact push_eq
    · refine' ⟨.none, .intro, _⟩; rw [← eq_ex]; exact push_eq
  · rename_i neg
    apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false neg conj.2⟩)
    clear neg; simp at eq
    okStep1 eq evm'
    split at eq
    · rename_i pos
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_true pos conj.2⟩)
      refine' ⟨.none, .intro, eq⟩
    · rename_i neg
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false neg conj.2⟩)
      clear neg
      okStep1 eq msg
      have notLimited' : (processCreateMessage false msg lim).Fit := by
        intro pm_eq
        rcases Except.of_toError?_eq_some _ _ pm_eq with ⟨_, rw⟩
        rw [← eq, rw] at notLimited; cases notLimited rfl
      rcases of_processCreateMessage _ _ _ notLimited' rfl
        with ⟨xl, good, pm⟩
      refine' ⟨xl, good_of_good_of_fit (by omega) notLimited' good, _, pm, _⟩
      bind_step' eq _
      split at eq
      · rename_i pos; rw [if_pos pos]; exact eq
      · rename_i neg; rw [if_neg neg]; exact eq

lemma of_genericCall {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {lim : Nat} {ex : Execution}
    (notLimited : ex.Fit)
    ( eq :
      genericCall false sevm devm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles lim = ex ) :
    ∃ xl : Xlot,
      xl.Good lim ex ∧
      GenericCall sevm devm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles xl ex := by
  rcases lim with _ | lim <;> simp only [genericCall] at eq
  {rw [← eq] at notLimited; cases notLimited rfl}
  okStep1 eq _; split at eq
  { rename_i pos; refine' ⟨.none, .intro, _⟩
    simp only [bind_pure] at eq;
    simp only []; rw [if_pos pos, eq] }
  rename_i neg
  apply Exists.imp (λ _ (h' : _ ∧ _) => ⟨h'.1, ite_of_false neg h'.2⟩);
  simp only [pure_bind] at eq
  okStep1 eq _; okStep1 eq msg
  have notLimited' :
    (processMessage false msg lim).Fit := by
    intro pm_eq
    rcases Except.of_toError?_eq_some _ _ pm_eq with ⟨_, rw⟩
    rw [← eq, rw] at notLimited
    cases notLimited rfl
  rcases of_processMessage msg lim _ notLimited' rfl
    with ⟨xl, good, pm⟩
  refine' ⟨_, good_of_good_of_fit (by omega) notLimited' good, _, pm, _⟩

  bind_step' eq _
  split at eq
  · rename_i pos; rw [if_pos pos]; bind_step' eq _; exact eq
  · rename_i neg; rw [if_neg neg]; bind_step' eq _; exact eq

lemma Xinst.run_of_run_eq
    {sevm : Sevm} {devm : Devm} {x : Xinst} {lim : Nat} {exn}
    (notLimited : exn.Fit) (eq : Xinst.run false sevm devm x lim = exn) :
    ∃ xl : Xlot, xl.Good lim exn ∧ Xinst.Run sevm devm x xl exn :=
  match x, lim with
  | _, 0 => by
    simp only [Xinst.run] at eq
    rw [← eq] at notLimited
    cases notLimited rfl
  | create, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 3 (bind_step_good eq _)
    okStep1 eq _; okStep1 eq _;

    bind_step_good eq _;
    okStep1 eq _; okStep1 eq _;
    rcases of_genericCreate notLimited eq with ⟨xl, good, gc⟩
    refine' ⟨_, good_of_good_of_fit (by omega) notLimited good, gc⟩
  | .create2, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 4 (bind_step_good eq _)
    iterate 3 (okStep1 eq _)
    bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    rcases of_genericCreate notLimited eq with ⟨xl, good, gc⟩
    refine' ⟨_, good_of_good_of_fit (by omega) notLimited good, gc⟩
  | .call, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 6 (bind_step_good eq _)
    bind_step_good eq _
    iterate 8 (okStep1 eq _)
    iterate 2 (bind_step_good eq _)
    okStep1 eq _; okStep1 eq _; split at eq
    · rename_i lt; refine' ⟨.none, .intro, _⟩
      simp only []; rw [if_pos lt]
      bind_step' eq _; exact eq
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      rcases of_genericCall notLimited eq with ⟨xl, good, gc⟩
      refine' ⟨_, good_of_good_of_fit (by omega) notLimited good, gc⟩
  | .callcode, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 7 bind_step_good eq _
    iterate 7 okStep1 eq _
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; split at eq
    · rename_i lt; refine' ⟨.none, .intro, _⟩
      simp only []; rw [if_pos lt]
      bind_step' eq _; exact eq
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      rcases of_genericCall notLimited eq with ⟨xl, good, gc⟩
      refine' ⟨_, good_of_good_of_fit (by omega) notLimited good, gc⟩
  | .delcall, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 6 bind_step_good eq _
    iterate 6 okStep1 eq _
    bind_step_good eq _; okStep1 eq _
    rcases of_genericCall notLimited eq with ⟨xl, good, gc⟩
    refine' ⟨_, good_of_good_of_fit (by omega) notLimited good, gc⟩
  | .statcall, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 6 bind_step_good eq _
    iterate 6 okStep1 eq _
    bind_step_good eq _; okStep1 eq _;
    rcases of_genericCall notLimited eq with ⟨xl, good, gc⟩
    refine' ⟨_, good_of_good_of_fit (by omega) notLimited good, gc⟩

lemma Ninst.run_of_run_eq
    {pc} {sevm : Sevm} {devm : Devm} {n : Ninst} {lim : Nat} {exn}
    (fit : exn.Fit) (eq : Ninst.run false ⟨pc, sevm, devm⟩ n lim = exn) :
    ∃ xl : Xlot,
      xl.Good lim exn ∧
      Ninst.Run' pc sevm devm n xl exn :=
  match n, lim with
  | push xs lt, lim => by
    refine' ⟨.none, .intro, _⟩
    simp only [Ninst.run] at eq; apply eq
  | reg r, _ => by
    simp [Ninst.run] at eq
    refine' ⟨.none, .intro, eq⟩
  | exec _, 0 => by
    simp only [Ninst.run] at eq
    rw [← eq] at fit; cases fit rfl
  | exec x, lim + 1 => by
    simp only [Ninst.run] at eq
    --have fit' := Except.fit_of_fit fit eq
    rcases Xinst.run_of_run_eq fit eq with ⟨xl, good, run⟩   --(cast_fit fit) eq
    refine' ⟨xl, good_of_good_of_fit (by omega) fit good, run⟩ --, run, _⟩

def of_exec :
    ∀ (lim : Nat) (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      exn.Fit → (exec false ⟨pc, sevm, devm⟩ lim = exn) →
      Nonempty (Exec pc sevm devm exn) := by
  apply Nat.strongRec; intro lim ih pc sevm devm exn fit exec_eq;
  cases lim with
  | zero =>
    rw [← exec_eq] at fit
    simp [exec, Except.toError?, Except.Fit, Except.Lim] at fit
  | succ lim =>
    simp [exec] at exec_eq
    rcases Option.eq_none_or_eq_some (Evm.getInst ⟨pc, sevm, devm⟩) with
      getInst_eq | ⟨i, getInst_eq⟩
      <;> rw [getInst_eq] at exec_eq
      <;> simp [Option.toExcept] at exec_eq
    · rw [← Except.of_error_bind_eq _ exec_eq]
      constructor; apply Exec.invOp getInst_eq
    · rw [ok_bind] at exec_eq
      rcases i with l | n | j <;> simp only [] at exec_eq
      · constructor;
        apply Exec.last getInst_eq exec_eq
      · rcases of_bind_eq exec_eq with
          ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
        · rw [ex_eq] at fit
          rcases Ninst.run_of_run_eq fit run_eq
            with ⟨_ | ⟨evm', ex'⟩, good, run⟩
          · rw [ex_eq]; constructor
            exact Exec.nextNoneErr getInst_eq run
          · rw [ex_eq];
            have ne_ex : Nonempty (Exec evm'.pc evm'.sta evm'.dyna ex') := by
              rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
              have fit' : ex'.Fit := by
                intro h; cases fit <| notLimited_of h
              apply @ih _ (by omega) _ _ _ _ fit' exec_eq'
            rcases ne_ex with ⟨exc⟩; constructor
            apply Exec.nextSomeErr getInst_eq run exc
        · rcases Ninst.run_of_run_eq (by {intro h; cases h}) run_eq
            with ⟨_ | ⟨evm', ex'⟩, good, run⟩
          · rcases (ih _ (by omega) _ _ _ _ fit ex_eq) with ⟨exc⟩
            constructor
            exact @Exec.nextNoneRec _ _ _ _ _ _ getInst_eq run exc
          · rcases good with ⟨lim', lt, exec_eq', notLimited_of⟩
            have fit' : ex'.Fit := by intro h; cases notLimited_of h
            rcases @ih _ (by omega) _ _ _ _ fit' exec_eq' with ⟨ih'⟩
            rcases @ih _ (by omega) _ _ _ _ fit ex_eq with ⟨ih''⟩
            constructor
            apply @Exec.nextSomeRec _ _ _ _ _ _ _ _ _ _ getInst_eq run ih' ih''
      · rcases of_bind_eq exec_eq
          with ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
        · rw [ex_eq]; constructor
          exact @Exec.jumpErr pc sevm devm j es.1 es.2 getInst_eq run_eq
        · rcases ih _ (Nat.lt_succ_self _) _ _ _ _ fit ex_eq with ⟨ih'⟩
          constructor; apply Exec.jumpRec getInst_eq run_eq ih'

lemma exec_iff_exec (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔
      (exn.Fit ∧ ∃ lim, exec false ⟨pc, sevm, devm⟩ lim = exn) := by
  constructor
  · intro ⟨exc⟩;
    rcases of_exec' _ _ _ _ exc with ⟨fit, lim, eq⟩
    refine ⟨fit, lim + 1, eq (lim + 1) (by omega)⟩
  · intro ⟨fit, lim, eq⟩; exact of_exec _ _ _ _ _ fit eq
