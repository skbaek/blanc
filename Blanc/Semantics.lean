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

def Xlot : Type := Option (Sevm × Devm × Execution)

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
  ( createdAccounts :
    rels.createdAccounts devm.createdAccounts devm'.createdAccounts )
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

def Except.SplitXl {ξ υ ζ : Type}
    (e : Except ξ υ) (xl : Xlot) (e' : Except ξ ζ) (q : υ → Prop) : Prop :=
  (∃ x, e = .error x ∧ e' = .error x ∧ xl = .none) ∨ (∃ y : υ, e = .ok y ∧ q y)

def ExecuteCode (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
  let evm : Evm := initEvm msg
  match msg.codeAddress with
  | .none =>
    ∃ ex', xl = .some ⟨evm.sta, evm.dyna, ex'⟩ ∧ executeCode.handleError ex' = ex
  | .some adr =>
    if adr.isPrecomp then
      (xl = .none ∧  executeCode.handleError (executePrecomp evm adr) = ex)
    else
      ∃ ex', xl = .some ⟨evm.sta, evm.dyna, ex'⟩ ∧ executeCode.handleError ex' = ex

def ProcessMessage (msg : Msg) (xl : Xlot)
    (ex : Except (String × State × AdrSet × Tra) Devm) : Prop :=
    msg.benvAfterTransfer.SplitXl xl ex <|
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
        (memorySize ≤ maxInitCodeSize)
        ⟨"OutOfGasError", devm⟩ ).SplitXl xl ex <|
  λ _ =>
    ExistsEq (addAccessedAddress devm newAddress) <|
  λ devm1 =>
    ExistsEq (except64th devm1.gasLeft) <|
  λ createMsgGas =>
    ExistsEq ({devm1 with gasLeft := devm1.gasLeft - createMsgGas}) <|
  λ devm2 =>
    (assertDynamic sevm devm2).SplitXl xl ex <|
  λ _ =>
    ExistsEq ({devm2 with returnData := []}) <|
  λ devm3 =>
    ExistsEq (devm3.state.get sevm.currentTarget) <|
  λ sender =>
   if (sender.bal < endowment ∨ sender.nonce = B64.max ∨ sevm.depth = 0) then
     (xl = .none ∧ {devm3 with gasLeft := devm3.gasLeft + createMsgGas}.push 0 = ex)
   else
   ExistsEq (devm3.incrNonce sevm.currentTarget) <|
  λ devm4 =>
    if
      ( let target := devm4.state.get newAddress
        target.nonce ≠ (0 : B64) ∨ target.code.size ≠ 0 ∨ target.stor.size ≠ 0 ) then
      (xl = .none ∧ devm4.push 0 = ex)
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
        depth := sevm.depth - 1
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
    ExistsEq (devm.withReturnData []) <|
  λ evm1 =>
    if (sevm.depth = 0) then
      (xl = .none ∧ (evm1.withGasLeft (evm1.gasLeft + gas)).push 0 = ex)
    else
    ExistsEq (evm1.memory.data.sliceD input_index input_size 0) <|
  λ calldata =>
    ExistsEq
      ( callMsg sevm evm1 gas value caller target codeAddress
          shouldTransferValue isStaticcall calldata code disablePrecompiles ) <|
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
      (devm.pop).SplitXl xl ex <|
    λ ⟨endowment, devm1⟩ =>
      (devm1.popToNat).SplitXl xl ex <|
    λ ⟨memoryIndex, devm2⟩ =>
      (devm2.popToNat).SplitXl xl ex <|
    λ ⟨memorySize, devm3⟩ =>
      ExistsEq (devm3.extCost [⟨memoryIndex, memorySize⟩]) <|
    λ extendCost =>
      ExistsEq (gasInitCodeWordCost * (ceilDiv memorySize 32)) <|
    λ initCodeCost =>
      (chargeGas (gasCreate + extendCost + initCodeCost) devm3).SplitXl xl ex <|
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
      (devm.pop).SplitXl xl ex <|
    λ ⟨endowment, devm1⟩ =>
      (devm1.popToNat).SplitXl xl ex <|
    λ ⟨memoryIndex, devm2⟩ =>
      (devm2.popToNat).SplitXl xl ex <|
    λ ⟨memorySize, devm3⟩ =>
      (devm3.pop).SplitXl xl ex <|
    λ ⟨salt, devm4⟩ =>
      ExistsEq (devm4.extCost [⟨memoryIndex, memorySize⟩]) <|
    λ extendCost =>
      ExistsEq (gasKeccak256Word * ceilDiv memorySize 32) <|
    λ initCodeHashCost =>
      ExistsEq (gasInitCodeWordCost * (ceilDiv memorySize 32)) <|
    λ initCodeCost =>
      (chargeGas (gasCreate + initCodeHashCost + extendCost + initCodeCost) devm4).SplitXl xl ex <|
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
      (devm.pop).SplitXl xl ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).SplitXl xl ex <|
    λ ⟨callee, devm2⟩ =>
      (devm2.pop).SplitXl xl ex <|
    λ ⟨value, devm3⟩ =>
      (devm3.popToNat).SplitXl xl ex <|
    λ ⟨inputIndex, devm4⟩ =>
      (devm4.popToNat).SplitXl xl ex <|
    λ ⟨inputSize, devm5⟩ =>
      (devm5.popToNat).SplitXl xl ex <|
    λ ⟨outputIndex, devm6⟩ =>
      (devm6.popToNat).SplitXl xl ex <|
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
      (chargeGas (msgCallCost + extendCost) devm9).SplitXl xl ex <|
    λ devm10 =>
      (Except.assert (!sevm.isStatic ∨ value = 0) ⟨"WriteInStaticContext", devm10⟩).SplitXl xl ex <|
    λ _ =>
      ExistsEq (devm10.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ devm11 =>
      ExistsEq ((devm11.getAcct sevm.currentTarget).bal) <|
    λ senderBal =>
      if senderBal < value then
          (devm11.push 0).SplitXl xl ex <|
        λ devm12 =>
          xl = .none ∧
          .ok ((devm12.withReturnData []).withGasLeft (devm12.gasLeft + msgCallStipend)) = ex
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
      (devm.pop).SplitXl xl ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).SplitXl xl ex <|
    λ ⟨codeAddress, devm2⟩ =>
      (devm2.pop).SplitXl xl ex <|
    λ ⟨value, devm3⟩ =>
      (devm3.popToNat).SplitXl xl ex <|
    λ ⟨inputIndex, devm4⟩ =>
      (devm4.popToNat).SplitXl xl ex <|
    λ ⟨inputSize, devm5⟩ =>
      (devm5.popToNat).SplitXl xl ex <|
    λ ⟨outputIndex, devm6⟩ =>
      (devm6.popToNat).SplitXl xl ex <|
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
      (chargeGas (msgCallCost + extendCost) devm9).SplitXl xl ex <|
    λ devm10 =>
      ExistsEq (devm10.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]) <|
    λ devm11 =>
      ExistsEq (devm11.getAcct sevm.currentTarget).bal <|
    λ senderBal =>
      if senderBal < value then
          (devm11.push 0).SplitXl xl ex <|
        λ devm12 =>
          xl = .none ∧
          .ok ((devm12.withReturnData []).withGasLeft (devm12.gasLeft + msgCallStipend)) = ex
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
      (devm.pop).SplitXl xl ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).SplitXl xl ex <|
    λ ⟨codeAddress, devm2⟩ =>
      (devm2.popToNat).SplitXl xl ex <|
    λ ⟨inputIndex, devm3⟩ =>
      (devm3.popToNat).SplitXl xl ex <|
    λ ⟨inputSize, devm4⟩ =>
      (devm4.popToNat).SplitXl xl ex <|
    λ ⟨outputIndex, devm5⟩ =>
      (devm5.popToNat).SplitXl xl ex <|
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
      (chargeGas (msgCallCost + extendCost) devm8).SplitXl xl ex <|
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
      (devm.pop).SplitXl xl ex <|
    λ ⟨gas, devm1⟩ =>
      (devm1.popToAdr).SplitXl xl ex <|
    λ ⟨target, devm2⟩ =>
      (devm2.popToNat).SplitXl xl ex <|
    λ ⟨inputIndex, devm3⟩ =>
      (devm3.popToNat).SplitXl xl ex <|
    λ ⟨inputSize, devm4⟩ =>
      (devm4.popToNat).SplitXl xl ex <|
    λ ⟨outputIndex, devm5⟩ =>
      (devm5.popToNat).SplitXl xl ex <|
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
      (chargeGas (msgCallCost + extendCost) devm8).SplitXl xl ex <|
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
  | .push xs _, .none, exn =>
    ( do let devm' ← chargeGas (if xs = [] then gBase else gVerylow) devm
         (devm'.push xs.toB256) ) = exn
  | .reg r, .none, exn =>
    Rinst.run ⟨pc, sevm, devm⟩ r = exn
  | .exec x, xl, exn =>
    Xinst.Run sevm devm x xl exn
  | _, _, _ => False

def Except.IsError {ξ υ : Type} (e : Except ξ υ) : Prop :=
  match e with
  | .error _ => True
  | .ok _ => False

/- Exec evm ex is provable iff
    ∃ lim : Nat, exec evm lim = ex
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
    {pc} {sevm} {devm} {n} {sevm_} {devm_} {exn_} {err} {devm'} :
    n.At sevm.code pc →
    Ninst.Run' pc sevm devm n
      (.some ⟨sevm_, devm_, exn_⟩)
      (.error ⟨err, devm'⟩) →
    Exec 0 sevm_ devm_ exn_ →
    Exec pc sevm devm (.error ⟨err, devm'⟩)
  | nextNoneRec {pc} {sevm : Sevm} {devm} {n} {devm'} {exn} :
    n.At sevm.code pc →
    Ninst.Run' pc sevm devm n .none (.ok devm') →
    Exec (pc + n.size) sevm devm' exn →
    Exec pc sevm devm exn
  | nextSomeRec
    {pc} {sevm} {devm} {n} {sevm_} {devm_}
    {exn_ : Execution} {devm'} {exn} :
    n.At sevm.code pc →
    Ninst.Run' pc sevm devm n
      (.some ⟨sevm_, devm_, exn_⟩)
      (.ok devm') →
    Exec 0 sevm_ devm_ exn_ →
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
  | .some ⟨sevm, devm, exn⟩ => Nonempty (Exec 0 sevm devm exn)

def Ninst.Run (sevm : Sevm) (devm : Devm) (n : Ninst) (devm' : Devm) : Prop :=
  ∃ xl : Xlot, xl.Filled ∧ ∃ pc, Ninst.Run' pc sevm devm n xl (.ok devm')

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
  Func.Run (p.main :: p.aux) sevm devm (.call 0) devm'

-------------------------------------------------------------------------------



/- Machinery for reasoning about fuel-bounded (`Fueled`) computations.
   A completed run is witnessed by an equation `f lim = Fueled.ofExcept ex`;
   fuel exhaustion (`Fueled.exhausted`) is ruled out by the mere shape of such
   an equation, so no `≠ "RecursionLimit"` side conditions are needed. -/

namespace Fueled

variable {ε ζ : Type} {α β : Type}

lemma ext {x y : Fueled ε α} (h : x.run = y.run) : x = y := h

lemma exhausted_ne_ofExcept {x : Except ε α} :
    (Fueled.exhausted : Fueled ε α) ≠ Fueled.ofExcept x :=
  fun h => nomatch congrArg ExceptT.run h

lemma ofExcept_ne_exhausted {x : Except ε α} :
    (Fueled.ofExcept x : Fueled ε α) ≠ Fueled.exhausted :=
  fun h => nomatch congrArg ExceptT.run h

lemma ne_exhausted_of_eq_ofExcept {x : Fueled ε α} {ex : Except ε α}
    (h : x = Fueled.ofExcept ex) : x ≠ Fueled.exhausted := by
  rw [h]; exact ofExcept_ne_exhausted

@[simp] lemma ofExcept_inj {x y : Except ε α} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.ofExcept y ↔ x = y :=
  ⟨fun h => Option.some.inj (congrArg ExceptT.run h), fun h => by rw [h]⟩

@[simp] lemma ok_inj {x y : α} :
    (Fueled.ok x : Fueled ε α) = Fueled.ok y ↔ x = y :=
  ofExcept_inj.trans ⟨Except.ok.inj, congrArg _⟩

@[simp] lemma error_inj {e e' : ε} :
    (Fueled.error e : Fueled ε α) = Fueled.error e' ↔ e = e' :=
  ofExcept_inj.trans ⟨Except.error.inj, congrArg _⟩

@[simp] lemma ok_ne_error {x : α} {e : ε} :
    (Fueled.ok x : Fueled ε α) = Fueled.error e ↔ False :=
  ⟨fun h => nomatch ofExcept_inj.mp h, False.elim⟩

@[simp] lemma error_ne_ok {x : α} {e : ε} :
    (Fueled.error e : Fueled ε α) = Fueled.ok x ↔ False :=
  ⟨fun h => nomatch ofExcept_inj.mp h, False.elim⟩

@[simp] lemma exhausted_ne_ok {x : α} :
    (Fueled.exhausted : Fueled ε α) = Fueled.ok x ↔ False :=
  ⟨fun h => exhausted_ne_ofExcept h, False.elim⟩

@[simp] lemma exhausted_ne_error {e : ε} :
    (Fueled.exhausted : Fueled ε α) = Fueled.error e ↔ False :=
  ⟨fun h => exhausted_ne_ofExcept h, False.elim⟩

@[simp] lemma ok_ne_exhausted {x : α} :
    (Fueled.ok x : Fueled ε α) = Fueled.exhausted ↔ False :=
  ⟨fun h => ofExcept_ne_exhausted h, False.elim⟩

@[simp] lemma error_ne_exhausted {e : ε} :
    (Fueled.error e : Fueled ε α) = Fueled.exhausted ↔ False :=
  ⟨fun h => ofExcept_ne_exhausted h, False.elim⟩

@[simp] lemma exhausted_ne_ofExcept_iff {x : Except ε α} :
    (Fueled.exhausted : Fueled ε α) = Fueled.ofExcept x ↔ False :=
  ⟨fun h => exhausted_ne_ofExcept h, False.elim⟩

@[simp] lemma ofExcept_eq_ok_iff {x : Except ε α} {y : α} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.ok y ↔ x = .ok y := ofExcept_inj

@[simp] lemma ofExcept_eq_error_iff {x : Except ε α} {e : ε} :
    (Fueled.ofExcept x : Fueled ε α) = Fueled.error e ↔ x = .error e := ofExcept_inj

lemma ok_bind (y : α) (f : α → Fueled ε β) :
    (Fueled.ok y : Fueled ε α) >>= f = f y := rfl

lemma error_bind (e : ε) (f : α → Fueled ε β) :
    (Fueled.error e : Fueled ε α) >>= f = Fueled.error e := rfl

lemma exhausted_bind (f : α → Fueled ε β) :
    (Fueled.exhausted : Fueled ε α) >>= f = Fueled.exhausted := rfl

lemma ofExcept_ok_bind (y : α) (f : α → Fueled ε β) :
    Fueled.ofExcept (.ok y) >>= f = f y := rfl

lemma ofExcept_error_bind (e : ε) (f : α → Fueled ε β) :
    Fueled.ofExcept (.error e) >>= f = Fueled.ofExcept (.error e) := rfl

lemma lift_bind_lift {x : Except ε α} {g : α → Except ε β} :
    ((liftM x : Fueled ε α) >>= fun y => liftM (g y)) =
      (liftM (x >>= g) : Fueled ε β) := by
  cases x <;> rfl

lemma assert_eq (p : Prop) [Decidable p] (e : ε) :
    (Fueled.assert p e : Fueled ε Unit) =
      Fueled.ofExcept (Except.assert p e) := by
  by_cases hp : p
  · simp only [Fueled.assert, Except.assert, if_pos hp]; rfl
  · simp only [Fueled.assert, Except.assert, if_neg hp]; rfl

lemma mapResult_ofExcept (g : Except ε α → Except ζ β) (x : Except ε α) :
    Fueled.mapResult g (Fueled.ofExcept x) = Fueled.ofExcept (g x) := rfl

lemma mapResult_exhausted (g : Except ε α → Except ζ β) :
    Fueled.mapResult g (Fueled.exhausted : Fueled ε α) = Fueled.exhausted := rfl

def of_bind_eq {x : Fueled ε α} {f : α → Fueled ε β} {ex : Except ε β}
    (h : x >>= f = Fueled.ofExcept ex) :
    (∃ e, x = Fueled.ofExcept (.error e) ∧ ex = .error e) ∨
      (∃ y, x = Fueled.ofExcept (.ok y) ∧ f y = Fueled.ofExcept ex) := by
  have hrun : x.run >>= ExceptT.bindCont f = some ex := congrArg ExceptT.run h
  rcases hx : x.run with _ | ⟨e | y⟩ <;> rw [hx] at hrun
  · cases hrun
  · left; exact ⟨e, Fueled.ext hx, (Option.some.inj hrun).symm⟩
  · right; exact ⟨y, Fueled.ext hx, Fueled.ext hrun⟩

def of_lift_bind_eq {x : Except ε α} {f : α → Fueled ε β} {ex : Except ε β}
    (h : Fueled.ofExcept x >>= f = Fueled.ofExcept ex) :
    (∃ e, x = .error e ∧ ex = .error e) ∨
      (∃ y, x = .ok y ∧ f y = Fueled.ofExcept ex) := by
  rcases of_bind_eq h with ⟨e, hx, hex⟩ | ⟨y, hx, hf⟩
  · exact Or.inl ⟨e, ofExcept_inj.mp hx, hex⟩
  · exact Or.inr ⟨y, ofExcept_inj.mp hx, hf⟩

def of_bind_eq' {x : Fueled ε α} {f : α → Fueled ε β} {ex : Except ε β}
    (h : x >>= f = Fueled.ofExcept ex) :
    ∃ ex', x = Fueled.ofExcept ex' ∧
      Fueled.ofExcept ex' >>= f = Fueled.ofExcept ex := by
  rcases of_bind_eq h with ⟨e, hx, hex⟩ | ⟨y, hx, hf⟩
  · refine ⟨.error e, hx, ?_⟩; rw [ofExcept_error_bind, hex]
  · refine ⟨.ok y, hx, ?_⟩; rw [ofExcept_ok_bind]; exact hf

def of_bind_eq_ok {x : Fueled ε α} {f : α → Fueled ε β} {z : β}
    (h : x >>= f = Fueled.ok z) :
    ∃ y, x = Fueled.ok y ∧ f y = Fueled.ok z := by
  rcases of_bind_eq (ex := .ok z) h with ⟨e, _, hex⟩ | ⟨y, hx, hf⟩
  · cases hex
  · exact ⟨y, hx, hf⟩

def of_lift_bind_eq_ok {x : Except ε α} {f : α → Fueled ε β} {z : β}
    (h : Fueled.ofExcept x >>= f = Fueled.ok z) :
    ∃ y, x = .ok y ∧ f y = Fueled.ok z := by
  rcases of_lift_bind_eq (ex := .ok z) h with ⟨e, _, hex⟩ | ⟨y, hx, hf⟩
  · cases hex
  · exact ⟨y, hx, hf⟩

def of_mapResult_eq {g : Except ε α → Except ζ β} {x : Fueled ε α}
    {ex : Except ζ β} (h : Fueled.mapResult g x = Fueled.ofExcept ex) :
    ∃ ex', x = Fueled.ofExcept ex' ∧ g ex' = ex := by
  have hrun : x.run.map g = some ex := congrArg ExceptT.run h
  rcases hx : x.run with _ | ex' <;> rw [hx] at hrun
  · cases hrun
  · exact ⟨ex', Fueled.ext hx, Option.some.inj hrun⟩

lemma bind_eq_bind {x : Fueled ε α} {f g : α → Fueled ε β}
    (h : ∀ y, x = Fueled.ok y → f y = g y) : x >>= f = x >>= g := by
  rcases hx : x.run with _ | ⟨e | y⟩
  · apply Fueled.ext
    show x.run >>= ExceptT.bindCont f = x.run >>= ExceptT.bindCont g
    rw [hx]; rfl
  · apply Fueled.ext
    show x.run >>= ExceptT.bindCont f = x.run >>= ExceptT.bindCont g
    rw [hx]; rfl
  · have hxy : x = Fueled.ok y := Fueled.ext hx
    rw [hxy, ok_bind, ok_bind]; exact h y hxy

lemma ne_exhausted_of_bind {x : Fueled ε α} {f : α → Fueled ε β} {y : α}
    (h : x >>= f ≠ Fueled.exhausted) (eq : x = Fueled.ok y) :
    f y ≠ Fueled.exhausted := by
  intro hex; apply h; rw [eq, ok_bind, hex]

lemma head_ne_exhausted_of_bind {x : Fueled ε α} {f : α → Fueled ε β}
    (h : x >>= f ≠ Fueled.exhausted) : x ≠ Fueled.exhausted := by
  intro hex; apply h; rw [hex, exhausted_bind]

lemma mapResult_ne_exhausted {g : Except ε α → Except ζ β} {x : Fueled ε α}
    (h : Fueled.mapResult g x ≠ Fueled.exhausted) : x ≠ Fueled.exhausted := by
  intro hex; apply h; rw [hex, mapResult_exhausted]

lemma bind_eq_of_eq_ok_of_eq {x : Except ε α} {y : α} {z : Fueled ε β}
    {f : α → Fueled ε β} (eq_ok : x = .ok y) (eq : f y = z) :
    Fueled.ofExcept x >>= f = z := by
  rw [eq_ok, ofExcept_ok_bind]; exact eq

end Fueled

def Xlot.Good' : Xlot → Prop
  | .none => True
  | .some ⟨sevm, devm, ex⟩ =>
    ∃ lim, exec { pc := 0, sta := sevm, dyna := devm } lim = Fueled.ofExcept ex

lemma Except.of_error_bind_eq {ξ υ ζ : Type}
    {x : ξ} {f : υ → Except ξ ζ} (e : Except ξ ζ)
    (eq : (Except.error x) >>= f = e) : Except.error x = e := by
  simp [bind, Except.bind] at eq; exact eq

lemma error_bind {ξ υ ζ : Type}
    {x : ξ} {f : υ → Except ξ ζ} :
    (Except.error x) >>= f = Except.error x := rfl

def ok_bind {ξ : Type u} {υ ζ : Type v} {y : υ} {g : υ → Except ξ ζ} :
    (.ok y) >>= g = g y := rfl

lemma forall_gt_of_forall_gt_succ_pred {p : Nat → Prop} (n : Nat) :
    (∀ m > n, p (m.pred + 1)) → (∀ m > n, p m) := by
  intro fa m gt; rcases m with _ | m
  · cases Nat.not_lt_zero _ gt
  · apply fa (m + 1) gt

lemma exists_forall_gt_of_splitXl {ξ υ ζ} {x : Except (String × ξ) υ} {xl}
    {ex : Except (String × ξ) ζ} {p} {f : υ → ℕ → Fueled (String × ξ) ζ}
    (split : Except.SplitXl x xl ex p)
    (efg : ∀ y, x = .ok y → p y →
      ∃ lim, ∀ lim' > lim, f y lim' = Fueled.ofExcept ex) :
    ∃ lim, ∀ lim' > lim,
      (Fueled.ofExcept x >>= λ y => f y lim') = Fueled.ofExcept ex := by
  rcases split with ⟨e, he, he', hxl⟩ | ⟨y, hy, hy'⟩
  · refine ⟨0, λ _ _ => ?_⟩
    rw [he, he']
    rfl
  · have ⟨lim, hlim⟩ := efg y hy hy'
    refine ⟨lim, λ lim' hlim' => ?_⟩
    rw [hy]
    exact hlim lim' hlim'

syntax "efg_step_splitXl " ident : tactic
macro_rules
  | `(tactic| efg_step_splitXl $run) =>
    `(tactic|
      (try rw [Fueled.assert_eq]);
      apply exists_forall_gt_of_splitXl $run;
      clear $run; intro _ temp $run; clear temp
    )

def Saturates {ε υ} (n : Nat) (f : Nat → Fueled ε υ) : Prop :=
  f n ≠ Fueled.exhausted → ∀ m, n < m → (f n = f m)

structure Saturation (lim : Nat) : Prop where
  (executeCode : ∀ (msg : Msg), Saturates lim (executeCode msg))
  (processMessage : ∀ (msg : Msg), Saturates lim (processMessage msg))
  ( processCreateMessage :
    ∀ (msg : Msg), Saturates lim (processCreateMessage msg) )
  ( genericCreate :
    ∀ (sevm : Sevm) (devm : Devm)
      (endowment : B256) (newAddress : Adr)
      (memoryIndex : Nat) (memorySize : Nat),
      Saturates lim
        (genericCreate sevm devm endowment newAddress memoryIndex memorySize) )
  ( genericCall :
    ∀ (sevm : Sevm) (devm : Devm)
      (gas : Nat) (value : B256) (caller : Adr) (target : Adr)
      (codeAddress : Adr) (shouldTransferValue : Bool) (isStaticcall : Bool)
      (inputIndex :Nat) (inputSize : Nat) (outputIndex : Nat)
      (outputSize : Nat) (code : ByteArray) (disablePrecompiles: Bool),
      Saturates lim
        ( genericCall sevm devm gas value caller target codeAddress
            shouldTransferValue isStaticcall inputIndex inputSize outputIndex
            outputSize code disablePrecompiles ) )
  ( xinstRun :
    ∀ (sevm : Sevm) (devm : Devm) (x : Xinst),
      Saturates lim (Xinst.run sevm devm x) )
  (ninstRun : ∀ (evm : Evm) (n : Ninst), Saturates lim (Ninst.run evm n))
  (exec : ∀ (evm : Evm), Saturates lim (exec evm))

lemma Except.bind_eq_bind {ξ υ ζ} {e : Except ξ υ} {f g : υ → Except ξ ζ}
    (eq : ∀ x, e = Except.ok x → f x = g x) : e >>= f = e >>= g := by
  cases e; rfl; apply eq _ rfl

syntax "eee_bind " ident  : tactic
macro_rules
  | `(tactic| eee_bind $ne) => `(tactic|
      apply Fueled.bind_eq_bind;
      intro _ eq_ok;
      have temp := Fueled.ne_exhausted_of_bind $ne eq_ok; clear $ne eq_ok;
      rename' temp => $ne
    )

lemma saturation (lim : Nat) : Saturation lim := by
  induction lim
  case zero =>
    refine' ⟨_, _, _, _, _, _, _, _⟩
    · intro _ ne; simp only [executeCode] at ne; cases ne rfl
    · intro _ ne; simp only [processMessage] at ne; cases ne rfl
    · intro _ ne; simp only [processCreateMessage] at ne; cases ne rfl
    · intro _ _ _ _ _ _ ne; simp only [genericCreate] at ne; cases ne rfl
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ne;
      simp only [genericCall] at ne; cases ne rfl
    · intro _ _ x ne; cases x <;>
      {simp only [Xinst.run] at ne; cases ne rfl}
    · intro _ n ne; cases n
      · intro m _; simp only [Ninst.run]
      · simp only [Ninst.run] at ne; cases ne rfl
      · intro m _; simp only [Ninst.run]
    · intro _ ne; simp only [exec] at ne; cases ne rfl
  case succ lim ih =>
    refine' ⟨_, _, _, _, _, _, _, _⟩
    · intro _ ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [executeCode] at *
      split at ne
      · rw [ih.exec _ (Fueled.mapResult_ne_exhausted ne) lim' (by omega)]
      · split at ne
        · rename_i pos; rw [if_pos pos, if_pos pos]
        · rename_i neg; rw [if_neg neg, if_neg neg]
          rw [ih.exec _ (Fueled.mapResult_ne_exhausted ne) lim' (by omega)]
    · intro _ ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [processMessage] at *
      eee_bind ne
      rw [ih.executeCode _ (Fueled.head_ne_exhausted_of_bind ne) lim' (by omega)]
    · intro _ ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [processCreateMessage] at *
      rw [ih.processMessage _ (Fueled.head_ne_exhausted_of_bind ne) lim' (by omega)]
    · intro _ _ _ _ _ _ ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [genericCreate] at *
      iterate 8 (eee_bind ne);
      split; {rfl}
      rename_i neg; rw [if_neg neg] at ne; clear neg
      eee_bind ne; eee_bind ne; split; {rfl}
      rename_i neg; rw [if_neg neg] at ne; clear neg
      eee_bind ne; eee_bind ne
      have ne' := Fueled.mapResult_ne_exhausted (Fueled.head_ne_exhausted_of_bind ne)
      rw [ih.processCreateMessage _ ne' lim' (by omega)]
    · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [genericCall] at *
      eee_bind ne; split at ne
      · rename_i pos; rw [if_pos pos, if_pos pos]
      · rename_i neg; rw [if_neg neg, if_neg neg]
        iterate 3 (eee_bind ne)
        have ne' := Fueled.mapResult_ne_exhausted (Fueled.head_ne_exhausted_of_bind ne)
        rw [ih.processMessage _ ne' lim' (by omega)]
    · intro _ _ x ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      rcases x  with _ | _ | _ | _ | _ | _ <;> simp only [Xinst.run] at *
      · iterate 8 (eee_bind ne)
        rw [ih.genericCreate _ _ _ _ _ _ ne lim' (by omega)]
      · iterate 19 (eee_bind ne)
        split; {rfl}; rename_i neg
        rw [if_neg neg] at ne; clear neg
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ne lim' (by omega)]
      · iterate 17 (eee_bind ne)
        split; {rfl}; rename_i neg
        rw [if_neg neg] at ne; clear neg
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ne lim' (by omega)]
      · iterate 14 (eee_bind ne)
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ne lim' (by omega)]
      · iterate 10 (eee_bind ne)
        rw [ih.genericCreate _ _ _ _ _ _ ne lim' (by omega)]
      · iterate 14 (eee_bind ne)
        rw [ih.genericCall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ne lim' (by omega)]
    · intro _ n ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      rcases n  with _ | _ | _ <;> simp only [Ninst.run] at *
      rw [ih.xinstRun _ _ _ ne lim' (by omega)]
    · intro _ ne lim' lt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ lt}
      simp only [exec] at *; eee_bind ne; split
      · simp only at ne
        rw [← ih.ninstRun _ _ (Fueled.head_ne_exhausted_of_bind ne) lim' (by omega)]
        eee_bind ne; apply ih.exec _ ne lim' (by omega)
      · simp only at ne; eee_bind ne
        apply ih.exec _ ne lim' (by omega)
      · rfl

lemma initEvm_eq (msg : Msg) : initEvm msg = { pc := 0, sta := (initEvm msg).sta, dyna := (initEvm msg).dyna } := rfl

lemma of_execute_code' {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (good : xl.Good') (ec : ExecuteCode msg xl ex) :
    ∃ lim, ∀ lim' > lim, executeCode msg lim' = Fueled.ofExcept ex := by
  simp only [ExecuteCode] at ec; split at ec
  · rename (msg.codeAddress = none) => eq_none
    rcases ec with ⟨ex', xl_eq, eq_ex⟩
    rw [xl_eq] at good
    simp only [Xlot.Good'] at good
    rcases good with ⟨lim, eq_ex'⟩
    refine' ⟨lim + 1, _⟩
    intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [executeCode]
    rw [eq_none]; simp only
    rw [initEvm_eq msg]
    rw [← (saturation lim).exec _
          (Fueled.ne_exhausted_of_eq_ofExcept eq_ex') lim' (by omega)]
    rw [eq_ex', Fueled.mapResult_ofExcept, eq_ex]
  · rename Adr => adr
    rename (msg.codeAddress = some adr) => eq_some
    split at ec
    · rename_i pos
      refine' ⟨1, _⟩; intro lim' gt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
      simp only [executeCode, eq_some, if_pos pos]
      exact congrArg Fueled.ofExcept ec.2
    · rename_i neg; rcases ec with ⟨ex', xl_eq, eq_ex⟩
      rw [xl_eq] at good; simp only [Xlot.Good'] at good
      rcases good with ⟨lim, eq_ex'⟩
      refine' ⟨lim + 1, _⟩; intro lim' gt
      rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
      simp only [executeCode]
      rw [eq_some]; simp only
      rw [if_neg neg]
      rw [initEvm_eq msg]
      rw [← (saturation lim).exec _
            (Fueled.ne_exhausted_of_eq_ofExcept eq_ex') lim' (by omega)]
      rw [eq_ex', Fueled.mapResult_ofExcept, eq_ex]

lemma exists_forall_gt_ok_bind_eq {ε υ ζ : Type}
    {f : Nat → υ → Fueled ε ζ} {y : υ} {ex : Except ε ζ} :
    (∃ lim, ∀ lim' > lim, (f lim' y) = Fueled.ofExcept ex) →
    ∃ lim, ∀ lim' > lim, (Fueled.ok y >>= f lim') = Fueled.ofExcept ex := id

lemma bind_eq_of_eq_ok_of_eq {ξ υ ζ} {x : Except ξ υ} {y} {z : Except ξ ζ}
    {f : υ → Except ξ ζ} (eq_ok : x = .ok y) (eq : f y = z) : (x >>= f) = z := by
  rw [eq_ok]; exact eq

syntax "eq_split " ident : tactic
macro_rules
  | `(tactic| eq_split $eq) => `(tactic|
      have temp := $eq; clear $eq;
      rcases temp with ⟨⟨_, _, _⟩, rw', rw⟩ | ⟨_, eq', $eq⟩ <;> [
        (rw [rw', rw]; rfl);
        (apply Fueled.bind_eq_of_eq_ok_of_eq eq'; clear eq')
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

syntax "efg_step_exec " ident ident term:max : tactic
macro_rules
  | `(tactic| efg_step_exec $run $good $lem) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases temp with ⟨ex', runs, $run⟩;
      have temp := $lem $good runs;
      clear $good runs;
      rcases temp with ⟨lim, run_eq⟩;
      refine' ⟨lim + 1, _⟩;
      intro lim' gt;
      have gt' : lim'.pred > lim :=
      ( by cases lim' <;>
           [ (cases Nat.not_lt_zero _ gt);
             (exact Nat.lt_of_succ_lt_succ gt) ] );
      rw [run_eq lim'.pred gt'];
      (try rw [Fueled.mapResult_ofExcept]);
      clear gt gt' run_eq
    )

syntax "efg_end_exec " ident ident term:max : tactic
macro_rules
  | `(tactic| efg_end_exec $run $good $lem) =>
    `(tactic|
      have temp := $lem $good $run; clear $good $run;
      rcases temp with ⟨lim, run_eq⟩;
      refine' ⟨lim + 1, _⟩;
      intro lim' gt;
      have gt' : lim'.pred > lim :=
      ( by cases lim' <;>
           [ (cases Nat.not_lt_zero _ gt);
             (exact Nat.lt_of_succ_lt_succ gt) ] );
      rw [run_eq lim'.pred gt']
    )

lemma of_process_message' {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm} (good : xl.Good')
    (run : ProcessMessage msg xl ex) :
    ∃ lim, ∀ lim' > lim, processMessage msg lim' = Fueled.ofExcept ex := by
  simp only [ProcessMessage] at run
  apply Exists.imp forall_gt_of_forall_gt_succ_pred
  simp only [processMessage]
  efg_step_splitXl run
  efg_step_exec run good of_execute_code'
  eq_split run
  eq_ite run <;> exact congrArg Fueled.ofExcept run

lemma of_process_create_message' {msg : Msg} {xl : Xlot}
    {ex : Except (String × State × AdrSet × Tra) Devm} (good : xl.Good')
    (run : ProcessCreateMessage msg xl ex) :
    ∃ lim, ∀ lim' > lim, processCreateMessage msg lim' = Fueled.ofExcept ex := by
  simp only [ProcessCreateMessage] at run
  apply Exists.imp forall_gt_of_forall_gt_succ_pred
  simp only [processCreateMessage]
  efg_step_exec run good of_process_message'
  eq_split run; eq_ite run
  · split at run <;> rename_i rw <;> rw [rw]
    · exact congrArg Fueled.ofExcept run
    · eq_ite run <;> exact congrArg Fueled.ofExcept run
  · exact congrArg Fueled.ofExcept run

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

lemma ok_bind' {ε : Type} {υ ζ : Type} {y : υ}
    {f : υ → Fueled ε ζ} {z : Fueled ε ζ}
    (eq : f y = z) : (Fueled.ok y >>= f) = z := eq

syntax "efg_step_early " ident : tactic
macro_rules
  | `(tactic| efg_step_early $run) =>
    `(tactic|
      have temp := $run; clear $run;
      rcases or_of_ite temp with ⟨pos, $run⟩ | ⟨neg, $run⟩ <;> clear temp <;> [
        ( apply exists_forall_gt_imp (λ _ => ite_eq_left_of_true pos);
          (try simp only [bind_pure]); clear pos );
        ( apply exists_forall_gt_imp (λ _ => ite_eq_right_of_false neg ∘ ok_bind');
          clear neg )
      ]
    )

lemma of_generic_create' {sevm : Sevm} {devm : Devm} {endowment : B256} {newAddress : Adr}
    {memoryIndex memorySize : ℕ} {xl : Xlot} {ex : Execution} (good : xl.Good')
    (run : GenericCreate sevm devm endowment newAddress memoryIndex memorySize xl ex) :
    ∃ lim,
      ∀ lim' > lim,
        genericCreate sevm devm endowment
          newAddress memoryIndex memorySize lim' = Fueled.ofExcept ex := by
  simp only [GenericCreate] at run
  apply Exists.imp forall_gt_of_forall_gt_succ_pred
  simp only [genericCreate]
  efg_step_exists run; efg_step_splitXl run
  iterate 3 (efg_step_exists run)
  efg_step_splitXl run; iterate 2 (efg_step_exists run)
  efg_step_early run;
  {refine' ⟨0, _⟩; intro _ _; exact congrArg Fueled.ofExcept run.2}
  efg_step_exists run
  efg_step_early run;
  {refine' ⟨0, _⟩; intro _ _; exact congrArg Fueled.ofExcept run.2}
  efg_step_exists run
  efg_step_exec run good of_process_create_message'
  eq_split run; eq_ite run <;> exact congrArg Fueled.ofExcept run

lemma of_generic_call' {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {xl : Xlot} {ex : Execution} (good : xl.Good')
    ( run :
      GenericCall sevm devm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles xl ex ) :
    ∃ lim, ∀ lim' > lim,
      genericCall sevm devm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles lim' =
          Fueled.ofExcept ex := by
  simp only [GenericCall] at run
  apply Exists.imp forall_gt_of_forall_gt_succ_pred
  simp only [genericCall]; efg_step_exists run;
  efg_step_early run;
  {refine' ⟨0, _⟩; intro _ _; exact congrArg Fueled.ofExcept run.2}
  efg_step_exists run; efg_step_exists run;
  efg_step_exec run good of_process_message'; eq_split run
  eq_ite run <;> {eq_split run; exact congrArg Fueled.ofExcept run}

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
    ∃ lim, ∀ lim' > lim, Xinst.run sevm devm x lim' = Fueled.ofExcept ex := by
  cases x <;>
    ( apply Exists.imp forall_gt_of_forall_gt_succ_pred ;
      simp only [Xinst.run] )
  · iterate 3 (efg_step_splitXl run)
    iterate 2 (efg_step_exists run)
    efg_step_splitXl run
    iterate 2 (efg_step_exists run)
    efg_end_exec run good of_generic_create'
  · iterate 7 (efg_step_splitXl run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    efg_step_splitXl run; efg_step_splitXl run;
    efg_step_exists run; efg_step_exists run;
    efg_step_ite run
    · efg_step_splitXl run; refine ⟨0, λ _ _ => congrArg Fueled.ofExcept run.2⟩
    · efg_end_exec run good of_generic_call'
  · iterate 7 (efg_step_splitXl run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    iterate 2 (efg_step_exists run)
    efg_step_exists run;
    efg_step_splitXl run
    iterate 2 (efg_step_exists run)
    efg_step_ite run
    · efg_step_splitXl run; refine ⟨0, λ _ _ => congrArg Fueled.ofExcept run.2⟩
    · efg_end_exec run good of_generic_call'
  · iterate 6 (efg_step_splitXl run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    efg_step_exists run
    efg_step_exists run;
    efg_step_splitXl run
    efg_step_exists run
    efg_end_exec run good of_generic_call'
  · iterate 4 (efg_step_splitXl run)
    iterate 3 (efg_step_exists run)
    efg_step_splitXl run
    iterate 2 (efg_step_exists run)
    efg_end_exec run good of_generic_create'
  · iterate 6 (efg_step_splitXl run)
    iterate 3 (efg_step_exists run)
    efg_step_exists run;
    efg_step_exists run
    efg_step_exists run;
    efg_step_splitXl run
    efg_step_exists run
    efg_end_exec run good of_generic_call'

lemma Ninst.run_of_run' {pc} {sevm} {devm} {n : Ninst} (xl : Xlot)
    {ex} (good : xl.Good') (run : Ninst.Run' pc sevm devm n xl ex) :
    ∃ lim, ∀ lim' > lim,
      Ninst.run ⟨pc, sevm, devm⟩ n lim' = Fueled.ofExcept ex := by
  rcases n with r | x | ⟨xs, le⟩
  · cases xl
    · simp only [Ninst.Run'] at run
      refine ⟨0, λ _ _ => ?_⟩
      simp only [Ninst.run]
      exact congrArg Fueled.ofExcept run
    · revert run; simp [Ninst.Run']
  · simp only [Ninst.Run'] at run
    rcases Xinst.run_eq_of_run good run with ⟨lim, run_eq⟩
    refine' ⟨lim + 1, λ lim' gt => _⟩
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.run]
    apply run_eq lim' (by omega)
  · cases xl
    · simp only [Ninst.Run'] at run
      refine ⟨0, λ _ _ => ?_⟩
      simp only [Ninst.run]
      rw [Fueled.lift_bind_lift]
      exact congrArg Fueled.ofExcept run
    · revert run; simp [Ninst.Run']

lemma of_exec' :
    ∀ (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      Exec pc sevm devm exn →
      ∃ lim, ∀ lim' > lim, (exec ⟨pc, sevm, devm⟩ lim' = Fueled.ofExcept exn) := by
  apply Exec.rec
  · intro pc sevm devm eq; refine' ⟨0, _⟩
    intro lim' gt; cases lim'; {cases Nat.not_lt_zero _ gt}
    simp only [exec, Option.toExcept, Evm.getInst, eq]; rfl
  · intro pc sevm devm n err devm' nat run
    rcases Ninst.run_of_run' .none .intro run with ⟨lim, eq⟩
    refine' ⟨lim + 2, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, exec, Option.toExcept, nat, Fueled.ofExcept_ok_bind]
    rw [eq lim' (by omega)]; rfl
  · intro pc sevm devm n sevm_ devm_ exn_ exn devm' nat run exc ⟨limExec, exec_eq⟩
    rcases
      Ninst.run_of_run'
        (.some ⟨sevm_, devm_, exn_⟩)
        ⟨limExec + 1, exec_eq _ (by omega)⟩
        run
      with ⟨limRun, run_eq⟩
    refine' ⟨(max limExec limRun) + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, exec, Option.toExcept, nat, Fueled.ofExcept_ok_bind]
    rw [run_eq lim' (by omega)]; rfl
  · intro pc sevm devm n devm' exn nat run exc ⟨limExec, exec_eq⟩
    rcases Ninst.run_of_run' .none .intro run
      with ⟨limRun, run_eq⟩
    refine' ⟨(max limExec limRun) + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, exec, Option.toExcept, nat, Fueled.ofExcept_ok_bind]
    rw [run_eq lim' (by omega)]; apply exec_eq _ (by omega)
  · intro pc sevm devm n sevm_ devm_ exn_ devm' exn nat run exc_ exc
      ⟨limExec_, eq_⟩
      ⟨limExec, eq⟩
    rcases
      Ninst.run_of_run'
        (.some ⟨sevm_, devm_, exn_⟩)
        ⟨limExec_ + 1, eq_ _ (by omega)⟩
        run
      with ⟨limRun, run_eq⟩
    refine' ⟨max limRun limExec + 1, _⟩
    intro lim' gt; rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Ninst.At] at nat
    simp only [Evm.getInst, _root_.exec, Option.toExcept, nat, Fueled.ofExcept_ok_bind]
    rw [run_eq lim' (by omega)]
    apply eq _ (by omega)
  · intro pc sevm devm j err devm' nat run
    simp only [Jinst.At] at nat
    simp only [Jinst.Run] at run
    refine' ⟨0, _⟩; intro lim gt
    rcases lim with _ | lim; {cases Nat.not_lt_zero _ gt}
    simp only [Evm.getInst, exec, nat, Option.toExcept, Fueled.ofExcept_ok_bind, run]; rfl
  · intro pc sevm devm j pc' devm' exn jat run exc ⟨lim, exec_eq⟩
    simp only [Jinst.At] at jat
    simp only [Jinst.Run] at run
    refine' ⟨lim + 1, _⟩; intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Evm.getInst, exec, jat, Option.toExcept, Fueled.ofExcept_ok_bind, run]
    apply exec_eq _ (by omega)
  · intro pc sevm devm l exn lat run
    simp only [Linst.At] at lat
    simp only [Linst.Run] at run
    refine' ⟨0, _⟩; intro lim' gt
    rcases lim' with _ | lim'; {cases Nat.not_lt_zero _ gt}
    simp only [Evm.getInst, exec, lat, Option.toExcept, Fueled.ofExcept_ok_bind, run]

def Xlot.Good (lim : Nat) : Xlot → Prop
  | .none => True
  | .some ⟨sevm, devm, exn⟩ =>
    ∃ lim' < lim,
      exec { pc := 0, sta := sevm, dyna := devm } lim' = Fueled.ofExcept exn

syntax "bind_step_good " ident rcasesPat : tactic
macro_rules
  | `(tactic| bind_step_good $h $pat) => `(tactic|
      (try rw [Fueled.assert_eq] at $h:ident);
      rcases Fueled.of_lift_bind_eq $h with im | ⟨$pat, temp_eq, eq'⟩;
      { refine ⟨.none, .intro, .inl ?_⟩;
        first | exact im | (rcases im with ⟨x, h1, h2⟩; exact ⟨x, h1, h2, rfl⟩) };
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, Or.inr ⟨_, temp_eq, conj.2⟩⟩);
      clear temp_eq
    )

syntax "okStep1 " ident rcasesPat : tactic
macro_rules
  | `(tactic| okStep1 $h $pat1) => `(tactic|
      rcases Fueled.of_lift_bind_eq $h with ⟨_, ⟨_⟩, _⟩ | ⟨$pat1, temp_eq, eq'⟩;
      clear $h; rename' eq' => $h;
      apply Exists.imp
        (λ _ (conj : _ ∧ _) => ⟨conj.1, ⟨_, (Except.ok.inj temp_eq).symm, conj.2⟩⟩);
      clear temp_eq
    )

syntax "bind_step' " ident rcasesPat : tactic
macro_rules
  | `(tactic| bind_step' $h $pat) => `(tactic|
      (try rw [Fueled.assert_eq] at $h:ident);
      rcases Fueled.of_lift_bind_eq $h with im | ⟨$pat, temp_eq, eq'⟩;
      { left;
        first | exact im | (rcases im with ⟨x, h1, h2⟩; exact ⟨x, h1, h2, rfl⟩) };
      clear $h; rename' eq' => $h;
      right; refine' ⟨_, temp_eq, _⟩; clear temp_eq
    )

lemma ite_of_true {c : Prop} [Decidable c] {p q : Prop} :
    c → p → if c then p else q := by
  intro hc hp; rw [if_pos hc]; exact hp

lemma ite_of_false {c : Prop} [Decidable c] {p q : Prop} :
    ¬ c → q → if c then p else q := by
  intro hc hp; rw [if_neg hc]; exact hp

lemma of_executeCode {msg : Msg} {lim : Nat}
    {ex : Except (String × State × AdrSet × Tra) Devm}
    (eq : executeCode msg lim = Fueled.ofExcept ex) :
    ∃ xl : Xlot, xl.Good lim ∧ ExecuteCode msg xl ex := by
  rcases lim with _ | lim <;> simp only [executeCode] at eq
  {cases Fueled.exhausted_ne_ofExcept eq}
  split at eq
  · rename msg.codeAddress = .none => eq_none
    rcases Fueled.of_mapResult_eq eq with ⟨ex', hexec, hhe⟩
    refine'
      ⟨ .some ⟨(initEvm msg).sta, (initEvm msg).dyna, ex'⟩,
        ⟨lim, (by omega), _⟩, _ ⟩
    · rw [← initEvm_eq msg]; exact hexec
    · simp only [ExecuteCode]; rw [eq_none]; exact ⟨ex', rfl, hhe⟩
  · rename Adr => adr
    rename msg.codeAddress = .some adr => eq_some
    split at eq
    · rename_i pos; refine' ⟨.none, .intro, _⟩
      simp only [ExecuteCode]; rw [eq_some]
      simp only []; rw [if_pos pos]
      exact ⟨rfl, Fueled.ofExcept_inj.mp eq⟩
    · rename_i neg
      rcases Fueled.of_mapResult_eq eq with ⟨ex', hexec, hhe⟩
      refine'
        ⟨ .some ⟨(initEvm msg).sta, (initEvm msg).dyna, ex'⟩,
          ⟨lim, (by omega), _⟩, _ ⟩
      · rw [← initEvm_eq msg]; exact hexec
      · simp only [ExecuteCode]; rw [eq_some]
        simp only []; rw [if_neg neg]; exact ⟨ex', rfl, hhe⟩

lemma Xlot.good_mono {lim lim' : Nat} {xl : Xlot}
    (le : lim ≤ lim') (good : xl.Good lim) : xl.Good lim' := by
  rcases xl with _ | ⟨sevm, devm, exn⟩; {constructor}
  rcases good with ⟨k, lt, h⟩
  exact ⟨k, Nat.lt_of_lt_of_le lt le, h⟩

lemma of_processMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (eq : processMessage msg lim = Fueled.ofExcept ex) :
    ∃ xl : Xlot, xl.Good lim ∧ ProcessMessage msg xl ex := by
  rcases lim with _ | lim <;> simp only [processMessage] at eq
  {cases Fueled.exhausted_ne_ofExcept eq}
  bind_step_good eq _
  rcases Fueled.of_bind_eq' eq with ⟨ex', ec_eq, eq⟩
  rcases of_executeCode ec_eq with ⟨xl, good, ec⟩
  refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, _, ec, _⟩
  bind_step' eq _; split at eq
  · rename_i pos; rw [if_pos pos]; exact Fueled.ofExcept_inj.mp eq
  · rename_i neg; rw [if_neg neg]; exact Fueled.ofExcept_inj.mp eq

lemma of_processCreateMessage (msg : Msg) (lim : Nat)
    (ex : Except (String × State × AdrSet × Tra) Devm)
    (eq : processCreateMessage msg lim = Fueled.ofExcept ex) :
    ∃ xl : Xlot,
      xl.Good lim ∧
      ProcessCreateMessage msg xl ex := by
  rcases lim with _ | lim <;> simp only [processCreateMessage] at eq
  {cases Fueled.exhausted_ne_ofExcept eq}
  rcases Fueled.of_bind_eq' eq with ⟨ex', pm_eq, eq⟩
  rcases of_processMessage _ _ _ pm_eq with ⟨xl, good, pcm⟩
  refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, _, pcm, _⟩
  bind_step' eq evm'
  split at eq
  · rename_i pos; rw [if_pos pos]
    cases pcm_eq : processCreateMessage.chargeCodeGas evm'
    · simp only []
      rw [pcm_eq] at eq
      simp only [] at eq
      split at eq
      · rename_i pos'; rw [if_pos pos']; exact Fueled.ofExcept_inj.mp eq
      · rename_i neg'; rw [if_neg neg']; exact Fueled.ofExcept_inj.mp eq
    · rw [pcm_eq] at eq; exact Fueled.ofExcept_inj.mp eq
  · rename_i neg; rw [if_neg neg]; exact Fueled.ofExcept_inj.mp eq

lemma of_genericCreate
    {sevm : Sevm} {devm : Devm} {endow : B256} {newAdr : Adr}
    {memIndex memSize lim : ℕ} {ex : Execution}
    (eq : genericCreate sevm devm endow newAdr memIndex memSize lim =
      Fueled.ofExcept ex) :
    ∃ xl : Xlot,
      xl.Good lim ∧
      GenericCreate sevm devm endow newAdr memIndex memSize xl ex := by
  rcases lim with _ | lim <;> simp only [genericCreate] at eq
  {cases Fueled.exhausted_ne_ofExcept eq}
  okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _
  okStep1 eq _; bind_step_good eq _; okStep1 eq _; okStep1 eq _
  split at eq
  · rename_i pos
    apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_true pos conj.2⟩)
    refine' ⟨.none, .intro, _⟩
    simp only [bind_pure] at eq
    exact ⟨rfl, Fueled.ofExcept_inj.mp eq⟩
  · rename_i neg
    apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false neg conj.2⟩)
    clear neg
    okStep1 eq evm'
    split at eq
    · rename_i pos
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_true pos conj.2⟩)
      simp only [bind_pure] at eq
      refine' ⟨.none, .intro, rfl, Fueled.ofExcept_inj.mp eq⟩
    · rename_i neg
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false neg conj.2⟩)
      clear neg
      okStep1 eq msg
      rcases Fueled.of_bind_eq' eq with ⟨ex'', hmap, eq⟩
      rcases Fueled.of_mapResult_eq hmap with ⟨ex', hrec, hlift⟩
      rcases of_processCreateMessage _ _ _ hrec with ⟨xl, good, pm⟩
      refine' ⟨xl, Xlot.good_mono (Nat.le_succ _) good, _, pm, _⟩
      rw [← hlift] at eq
      bind_step' eq _
      split at eq
      · rename_i pos; rw [if_pos pos]; exact Fueled.ofExcept_inj.mp eq
      · rename_i neg; rw [if_neg neg]; exact Fueled.ofExcept_inj.mp eq

lemma of_genericCall {sevm : Sevm} {devm : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {input_index input_size output_index output_size : Nat} {code : ByteArray}
    {disablePrecompiles : Bool} {lim : Nat} {ex : Execution}
    ( eq :
      genericCall sevm devm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles lim =
          Fueled.ofExcept ex ) :
    ∃ xl : Xlot,
      xl.Good lim ∧
      GenericCall sevm devm gas value caller target codeAddress
        shouldTransferValue isStaticcall input_index input_size
        output_index output_size code disablePrecompiles xl ex := by
  rcases lim with _ | lim <;> simp only [genericCall] at eq
  {cases Fueled.exhausted_ne_ofExcept eq}
  okStep1 eq _; split at eq
  { rename_i pos; refine' ⟨.none, .intro, _⟩
    simp only [bind_pure] at eq
    simp only []; rw [if_pos pos]
    exact ⟨trivial, Fueled.ofExcept_inj.mp eq⟩ }
  rename_i neg
  apply Exists.imp (λ _ (h' : _ ∧ _) => ⟨h'.1, ite_of_false neg h'.2⟩)
  simp only [pure_bind] at eq
  okStep1 eq _; okStep1 eq msg
  rcases Fueled.of_bind_eq' eq with ⟨ex'', hmap, eq⟩
  rcases Fueled.of_mapResult_eq hmap with ⟨ex', hrec, hlift⟩
  rcases of_processMessage _ _ _ hrec with ⟨xl, good, pm⟩
  refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, _, pm, _⟩
  rw [← hlift] at eq
  bind_step' eq _
  split at eq
  · rename_i pos; rw [if_pos pos]; bind_step' eq _
    exact Fueled.ofExcept_inj.mp eq
  · rename_i neg; rw [if_neg neg]; bind_step' eq _
    exact Fueled.ofExcept_inj.mp eq

lemma Xinst.run_of_run_eq
    {sevm : Sevm} {devm : Devm} {x : Xinst} {lim : Nat} {exn}
    (eq : Xinst.run sevm devm x lim = Fueled.ofExcept exn) :
    ∃ xl : Xlot, xl.Good lim ∧ Xinst.Run sevm devm x xl exn :=
  match x, lim with
  | _, 0 => by
    simp only [Xinst.run] at eq
    cases Fueled.exhausted_ne_ofExcept eq
  | create, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 3 (bind_step_good eq _)
    okStep1 eq _; okStep1 eq _;
    bind_step_good eq _;
    okStep1 eq _; okStep1 eq _;
    rcases of_genericCreate eq with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, gc⟩
  | .create2, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 4 (bind_step_good eq _)
    iterate 3 (okStep1 eq _)
    bind_step_good eq _; okStep1 eq _; okStep1 eq _;
    rcases of_genericCreate eq with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, gc⟩
  | .call, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 6 (bind_step_good eq _)
    bind_step_good eq _
    iterate 8 (okStep1 eq _)
    iterate 2 (bind_step_good eq _)
    okStep1 eq _; okStep1 eq _; split at eq
    · rename_i lt; refine' ⟨.none, .intro, _⟩
      simp only []; rw [if_pos lt]
      bind_step' eq _; exact ⟨trivial, Fueled.ofExcept_inj.mp eq⟩
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      rcases of_genericCall eq with ⟨xl, good, gc⟩
      refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, gc⟩
  | .callcode, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 7 bind_step_good eq _
    iterate 7 okStep1 eq _
    bind_step_good eq _; okStep1 eq _; okStep1 eq _; split at eq
    · rename_i lt; refine' ⟨.none, .intro, _⟩
      simp only []; rw [if_pos lt]
      bind_step' eq _; exact ⟨trivial, Fueled.ofExcept_inj.mp eq⟩
    · rename_i nlt
      apply Exists.imp (λ _ (conj : _ ∧ _) => ⟨conj.1, ite_of_false nlt conj.2⟩)
      rcases of_genericCall eq with ⟨xl, good, gc⟩
      refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, gc⟩
  | .delcall, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 6 bind_step_good eq _
    iterate 6 okStep1 eq _
    bind_step_good eq _; okStep1 eq _
    rcases of_genericCall eq with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, gc⟩
  | .statcall, lim + 1 => by
    simp only [Xinst.run] at eq
    iterate 6 bind_step_good eq _
    iterate 6 okStep1 eq _
    bind_step_good eq _; okStep1 eq _;
    rcases of_genericCall eq with ⟨xl, good, gc⟩
    refine' ⟨_, Xlot.good_mono (Nat.le_succ _) good, gc⟩

lemma Ninst.run_of_run_eq
    {pc} {sevm : Sevm} {devm : Devm} {n : Ninst} {lim : Nat} {exn}
    (eq : Ninst.run ⟨pc, sevm, devm⟩ n lim = Fueled.ofExcept exn) :
    ∃ xl : Xlot,
      xl.Good lim ∧
      Ninst.Run' pc sevm devm n xl exn :=
  match n, lim with
  | push xs lt, lim => by
    refine' ⟨.none, .intro, _⟩
    simp only [Ninst.run] at eq
    rw [Fueled.lift_bind_lift] at eq
    exact Fueled.ofExcept_inj.mp eq
  | reg r, _ => by
    simp only [Ninst.run] at eq
    exact ⟨.none, .intro, Fueled.ofExcept_inj.mp eq⟩
  | exec _, 0 => by
    simp only [Ninst.run] at eq
    cases Fueled.exhausted_ne_ofExcept eq
  | exec x, lim + 1 => by
    simp only [Ninst.run] at eq
    rcases Xinst.run_of_run_eq eq with ⟨xl, good, run⟩
    exact ⟨xl, Xlot.good_mono (Nat.le_succ _) good, run⟩

def of_exec :
    ∀ (lim : Nat) (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution),
      (exec ⟨pc, sevm, devm⟩ lim = Fueled.ofExcept exn) →
      Nonempty (Exec pc sevm devm exn) := by
  apply Nat.strongRec; intro lim ih pc sevm devm exn exec_eq
  cases lim with
  | zero =>
    simp only [exec] at exec_eq
    cases Fueled.exhausted_ne_ofExcept exec_eq
  | succ lim =>
    simp only [exec] at exec_eq
    rcases Option.eq_none_or_eq_some (Evm.getInst ⟨pc, sevm, devm⟩) with
      getInst_eq | ⟨i, getInst_eq⟩
      <;> rw [getInst_eq] at exec_eq
      <;> simp only [Option.toExcept] at exec_eq
    · have h : Except.error ("InvalidOpcode", devm) = exn := by
        rcases Fueled.of_lift_bind_eq exec_eq with ⟨e, he, hex⟩ | ⟨y, hy, _⟩
        · rw [hex, ← he]
        · cases hy
      rw [← h]; constructor; apply Exec.invOp getInst_eq
    · rw [Fueled.ofExcept_ok_bind] at exec_eq
      rcases i with l | n | j <;> simp only [] at exec_eq
      · constructor
        apply Exec.last getInst_eq (Fueled.ofExcept_inj.mp exec_eq)
      · rcases Fueled.of_bind_eq exec_eq with
          ⟨es, run_eq, ex_eq⟩ | ⟨evm', run_eq, ex_eq⟩
        · rcases Ninst.run_of_run_eq run_eq
            with ⟨_ | ⟨sevm', devm', ex'⟩, good, run⟩
          · rw [ex_eq]; constructor
            exact Exec.nextNoneErr getInst_eq run
          · rw [ex_eq]
            rcases good with ⟨lim', lt, exec_eq'⟩
            rcases ih _ (by omega) _ _ _ _ exec_eq' with ⟨exc⟩
            constructor
            apply Exec.nextSomeErr getInst_eq run exc
        · rcases Ninst.run_of_run_eq run_eq
            with ⟨_ | ⟨sevm', devm', ex'⟩, good, run⟩
          · rcases ih _ (by omega) _ _ _ _ ex_eq with ⟨exc⟩
            constructor
            exact @Exec.nextNoneRec _ _ _ _ _ _ getInst_eq run exc
          · rcases good with ⟨lim', lt, exec_eq'⟩
            rcases ih _ (by omega) _ _ _ _ exec_eq' with ⟨ih'⟩
            rcases ih _ (by omega) _ _ _ _ ex_eq with ⟨ih''⟩
            constructor
            exact Exec.nextSomeRec getInst_eq run ih' ih''
      · rcases Fueled.of_lift_bind_eq exec_eq
          with ⟨es, run_eq, ex_eq⟩ | ⟨pd, run_eq, ex_eq⟩
        · rw [ex_eq]; constructor
          exact @Exec.jumpErr pc sevm devm j es.1 es.2 getInst_eq run_eq
        · rcases ih _ (Nat.lt_succ_self _) _ _ _ _ ex_eq with ⟨ih'⟩
          constructor; apply Exec.jumpRec getInst_eq run_eq ih'

lemma exec_iff_exec_eq (pc : Nat) (sevm : Sevm) (devm : Devm) (exn : Execution) :
    Nonempty (Exec pc sevm devm exn) ↔
      ∃ lim, exec ⟨pc, sevm, devm⟩ lim = Fueled.ofExcept exn := by
  constructor
  · intro ⟨exc⟩
    rcases of_exec' _ _ _ _ exc with ⟨lim, eq⟩
    exact ⟨lim + 1, eq (lim + 1) (by omega)⟩
  · intro ⟨lim, eq⟩; exact of_exec _ _ _ _ _ eq
