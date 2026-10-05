import Blanc.ExecutionHistory
import Blanc.ExecutionTraceWarmth
import Blanc.ExecutionTraceAdmission
import Blanc.CommonProofs
import Blanc.LadderBase

/-!
# Per-frame calldata-length bound for configured histories

Every configured-history headline carries, inside its per-entered-frame
admission, the premise `sevm.data.length < 2 ^ 256`.  This module derives that
bound once, for every raw frame of a `ConfiguredHistoryTrace`, from the
validation the trace already retains — with no per-frame premise and no
block-level premise beyond what the trace itself validates.

Proof idea.
- Transaction roots: `validateTransaction` forces `tx.gas` above the intrinsic
  cost, whose calldata part is `4` gas per token with at least one token per
  byte, so `tx.data.length * 4 ≤ tx.gas`.  `checkTransaction` forces `tx.gas`
  below the block gas limit, and header validation (`checkGasLimit`, reached
  through `stateTransitionUsing`) keeps that limit below `2 ^ 63`.  The bound
  needs no fork-specific transaction cap.
- Child frames: CALL-family calldata is a memory slice whose size is a popped
  `B256.toNat` (hence `< 2 ^ 256`); CREATE-family calldata is `[]`.
- System-message roots carry `[]` or a `B256.toBytes` (32 bytes).
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-! ## Pure bounds: slices and intrinsic tokens -/

/-- A memory slice has exactly the requested length. -/
theorem Array.sliceD_length (xs : Array UInt8) (m n : Nat) (d : UInt8) :
    (Array.sliceD xs m n d).length = n := by
  rw [Array.sliceD_eq_map]
  simp only [Array.getD_eq_getD_getElem?, List.length_map, List.length_range]

/-- Intrinsic calldata tokens dominate the byte length: every byte costs at
least one token (zero bytes) and up to four (nonzero bytes). -/
theorem calldata_tokens_ge_length (l : Bytes) :
    l.length ≤
      l.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) 0 := by
  have aux : ∀ (c : Nat) (l : Bytes),
      l.length + c ≤
        l.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) c := by
    intro c l
    induction l generalizing c with
    | nil => simp only [List.length_nil, zero_add, List.foldl_nil, Std.le_refl]
    | cons x xs ih =>
      simp only [List.length_cons, List.foldl_cons]
      have h1 : 1 ≤ (if x = (0 : UInt8) then 1 else 4) := by
        split <;> omega
      have h2 := ih (c + (if x = (0 : UInt8) then 1 else 4))
      omega
  have h := aux 0 l
  simpa only [ge_iff_le, add_zero] using h

/-! ## Transaction validation implies the calldata bound -/

/-- From a successful legacy validation, the intrinsic cost sits below
`tx.gas`. -/
theorem validated_intrinsic_le_gas {rules : ForkRules} {tx : Tx} {sender : Adr}
    {p : Nat × Nat} (hsg : rules.stateGas = none)
    (h : validateTransaction rules tx sender = .ok p) :
    (calculateIntrinsicCost rules tx sender).1 ≤ tx.gas := by
  simp only [validateTransaction, hsg] at h
  by_cases hc : max (calculateIntrinsicCost rules tx sender).1
      (calculateIntrinsicCost rules tx sender).2 > tx.gas
  · simp only [hc, ↓reduceIte] at h
    obtain ⟨_, hcontra, _⟩ := Except.bind_eq_ok h
    cases hcontra
  · exact (Nat.le_max_left _ _).trans (not_lt.mp hc)

/-- The intrinsic cost dominates the calldata part: base, initcode, access-list
and authorization costs are all nonnegative. -/
theorem intrinsic_ge_dataCost {rules : ForkRules} {tx : Tx} {sender : Adr}
    (hsg : rules.stateGas = none) :
    (tx.data.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) 0) *
        standardCallDataTokenCost ≤
      (calculateIntrinsicCost rules tx sender).1 := by
  simp only [calculateIntrinsicCost, hsg, standardCallDataTokenCost]
  omega

/-- Validated calldata satisfies `length * 4 ≤ tx.gas`. -/
theorem tx_data_length_mul4_le_gas {rules : ForkRules} {tx : Tx} {sender : Adr}
    {p : Nat × Nat} (hsg : rules.stateGas = none)
    (h : validateTransaction rules tx sender = .ok p) :
    tx.data.length * 4 ≤ tx.gas := by
  have hi := validated_intrinsic_le_gas hsg h
  have ht := calldata_tokens_ge_length tx.data
  have hd := intrinsic_ge_dataCost (rules := rules) (tx := tx) (sender := sender) hsg
  simp only [standardCallDataTokenCost] at hd
  omega

/-- A checked legacy transaction fits in the block gas limit: the required gas
is `tx.gas` itself and success means it does not exceed what is available. -/
theorem tx_gas_le_blockGasLimit_of_checked {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {q : Adr × Nat × List B256 × Nat}
    (hsg : benv.stat.rules.stateGas = none)
    (h : checkTransaction benv bout tx = .ok q) :
    tx.gas ≤ benv.stat.blockGasLimit := by
  simp only [checkTransaction] at h
  obtain ⟨_, hlim, -⟩ := Except.bind_eq_ok h
  rw [Except.mapError_eq_ok_iff] at hlim
  simp only [checkTransactionGasLimits, hsg] at hlim
  by_cases hc : tx.gas > benv.stat.blockGasLimit - bout.blockGasUsed
  · simp only [hc, ↓reduceIte] at hlim
    cases hlim
  · simp only [hc, ↓reduceIte] at hlim
    omega

/-- A transitioned block's header gas limit is below `2 ^ 63`: `validateHeader`
runs `calculateBaseFeePerGas`, which runs `checkGasLimit`. -/
theorem ConfiguredBlockTrace.header_gasLimit_lt {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTrace cfg pre post) :
    trace.block.header.gasLimit < 2 ^ 63 := by
  have htrans := trace.transition
  have hId : cfg.chainId = pre.chainId :=
    stateTransitionUsing_success_chainId_eq htrans
  rw [stateTransitionUsing_eq_of_chainId_eq hId] at htrans
  obtain ⟨_, -, htrans⟩ := Except.bind_eq_ok htrans
  obtain ⟨hvh, -, -⟩ := stateTransitionAt_eq_ok htrans
  unfold validateHeader at hvh
  obtain ⟨parent, -, hvh⟩ := Except.bind_eq_ok hvh
  dsimp only at hvh
  by_cases hpar : trace.block.header.parentHash ≠
      (Header.toBLT parent.header).toBytes.keccak
  · simp only [ne_eq, hpar, not_false_eq_true, ↓reduceIte] at hvh
    by_cases hz : trace.block.header.parentHash = 0
    · simp only [hz, ↓reduceIte] at hvh
      obtain ⟨_, hcontra, _⟩ := Except.bind_eq_ok hvh
      cases hcontra
    · simp only [hz, ↓reduceIte] at hvh
      obtain ⟨_, hcontra, _⟩ := Except.bind_eq_ok hvh
      cases hcontra
  · simp only [hpar, ↓reduceIte] at hvh
    obtain ⟨_, hbase, -⟩ := Except.bind_eq_ok hvh
    rw [Except.mapError_eq_ok_iff] at hbase
    unfold calculateBaseFeePerGas at hbase
    dsimp only at hbase
    obtain ⟨_, hcl, -⟩ := Except.bind_eq_ok hbase
    unfold checkGasLimit at hcl
    by_cases hlim : trace.block.header.gasLimit ≥ gasLimitMaximum
    · simp only [hlim, ↓reduceIte] at hcl
      cases hcl
    · have hmax : gasLimitMaximum = 2 ^ 63 := rfl
      omega

/-! ## Message data is preserved by delegation -/

/-- A delegation step never touches the static environment or the calldata. -/
theorem setDelegationStep_preserves {auth : Auth} {msg : Msg} {rc : B256}
    {p : Msg × B256} (h : setDelegationStep auth msg rc = .ok p) :
    p.1.benv.stat = msg.benv.stat ∧ p.1.data = msg.data := by
  unfold setDelegationStep at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · split at h
    · cases h; exact ⟨rfl, rfl⟩
    · cases hrec : recoverAuthority auth with
      | error err =>
        cases err <;> simp only [hrec] at h
        all_goals (cases h; try exact ⟨rfl, rfl⟩)
      | ok authority =>
        simp only [hrec] at h
        repeat' split at h
        all_goals (cases h; exact ⟨rfl, rfl⟩)

/-- A delegation step never touches calldata. -/
theorem setDelegationStep_data {auth : Auth} {msg : Msg} {rc : B256}
    {p : Msg × B256} (h : setDelegationStep auth msg rc = .ok p) :
    p.1.data = msg.data :=
  (setDelegationStep_preserves h).2

/-- A delegation step never touches the static environment. -/
theorem setDelegationStep_benvStat {auth : Auth} {msg : Msg} {rc : B256}
    {p : Msg × B256} (h : setDelegationStep auth msg rc = .ok p) :
    p.1.benv.stat = msg.benv.stat :=
  (setDelegationStep_preserves h).1

/-- The delegation loop never touches calldata. -/
theorem setDelegationLoop_data :
    ∀ (auths : List Auth) {msg : Msg} {rc : B256} {p : Msg × B256},
      setDelegationLoop auths msg rc = .ok p → p.1.data = msg.data
  | [], _, _, _, hp => by cases hp; rfl
  | _ :: _, _, _, _, hp => by
    unfold setDelegationLoop at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact (setDelegationLoop_data _ hp).trans (setDelegationStep_data hq)

/-- The delegation loop never touches the static environment. -/
theorem setDelegationLoop_benvStat :
    ∀ (auths : List Auth) {msg : Msg} {rc : B256} {p : Msg × B256},
      setDelegationLoop auths msg rc = .ok p → p.1.benv.stat = msg.benv.stat
  | [], _, _, _, hp => by cases hp; rfl
  | _ :: _, _, _, _, hp => by
    unfold setDelegationLoop at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact (setDelegationLoop_benvStat _ hp).trans (setDelegationStep_benvStat hq)

/-- Delegation never touches calldata. -/
theorem setDelegation_data {msg : Msg} {p : Msg × B256}
    (h : setDelegation msg = .ok p) : p.1.data = msg.data := by
  unfold setDelegation at h
  obtain ⟨⟨q1, q2⟩, hq, h⟩ := Except.bind_eq_ok h
  have h1 := setDelegationLoop_data _ hq
  dsimp only at h
  split at h
  · obtain ⟨_, hbad, _⟩ := Except.bind_eq_ok h
    cases hbad
  · cases h; exact h1

/-- Delegation never touches the static environment. -/
theorem setDelegation_benvStat {msg : Msg} {p : Msg × B256}
    (h : setDelegation msg = .ok p) : p.1.benv.stat = msg.benv.stat := by
  unfold setDelegation at h
  obtain ⟨⟨q1, q2⟩, hq, h⟩ := Except.bind_eq_ok h
  have h1 := setDelegationLoop_benvStat _ hq
  dsimp only at h
  split at h
  · obtain ⟨_, hbad, _⟩ := Except.bind_eq_ok h
    cases hbad
  · cases h; exact h1

/-- The call wrapper preserves the delegated message's calldata. -/
theorem messageCallDelegation_data {msg : Msg} {p : Msg × Nat}
    (h : messageCallDelegation msg = .ok p) : p.1.data = msg.data := by
  unfold messageCallDelegation at h
  split at h
  · cases h; rfl
  · obtain ⟨q, hq, h⟩ := Except.bind_eq_ok h
    have h1 := setDelegation_data hq
    dsimp only at h
    cases h
    dsimp only
    exact h1

/-- The call wrapper preserves the delegated message's environment. -/
theorem messageCallDelegation_benvStat {msg : Msg} {p : Msg × Nat}
    (h : messageCallDelegation msg = .ok p) : p.1.benv.stat = msg.benv.stat := by
  unfold messageCallDelegation at h
  split at h
  · cases h; rfl
  · obtain ⟨q, hq, h⟩ := Except.bind_eq_ok h
    have h1 := setDelegation_benvStat hq
    dsimp only at h
    cases h
    dsimp only
    exact h1

/-- Resolving the delegation target preserves calldata. -/
theorem messageCallExecutionMessage_data (msg : Msg) :
    (messageCallExecutionMessage msg).data = msg.data := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-- Resolving the delegation target preserves the static environment. -/
theorem messageCallExecutionMessage_benvStat (msg : Msg) :
    (messageCallExecutionMessage msg).benv.stat = msg.benv.stat := by
  unfold messageCallExecutionMessage
  split <;> rfl

/-! ## Per-transaction and per-system-message bounds -/

/-- A validated, gas-fitting transaction has short calldata: intrinsic gas
charges at least one token per byte at `4` gas per token, and the transaction
gas fits under the block gas limit, which header validation keeps below
`2 ^ 63`.  The Osaka-and-later `2 ^ 24` transaction cap is not needed. -/
theorem TransactionTrace.data_length_lt {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork)
    (hgas : tx.gas ≤ benv.stat.blockGasLimit)
    (hlim : benv.stat.blockGasLimit < 2 ^ 63) :
    tx.data.length < 2 ^ 256 := by
  have hsg : benv.stat.rules.stateGas = none := hfork.rules_stateGas_none
  have hmul4 : tx.data.length * 4 ≤ tx.gas :=
    tx_data_length_mul4_le_gas hsg trace.validation
  have hbig : (2 : Nat) ^ 63 < 2 ^ 256 := by decide
  omega

/-- A system message carries exactly the data it was built with. -/
theorem systemTransactionMessage_data {benv : Benv} {target : Adr} {data : Bytes} :
    (systemTransactionMessage benv target data).data = data := rfl

/-- Fixed system data is short: `[]` or a 32-byte hash. -/
theorem systemData_length_lt {data : Bytes}
    (hdata : data = [] ∨ ∃ h : B256, data = h.toBytes) :
    data.length < 2 ^ 256 := by
  rcases hdata with rfl | ⟨h, rfl⟩
  · decide
  · rw [B256.length_toBytes]
    decide

/-! ## Entered children inherit slice-bounded calldata -/

/-- An entered frame's static data is its inner message's data. -/
theorem Frame.enter_data_eq {f : Frame} {cevm : Evm}
    (henter : f.enter = .run cevm) : cevm.sta.data = f.inner.data := by
  obtain ⟨benv, -, rfl⟩ := Frame.enter_run_inv henter
  rfl

/-- A call frame's inner data is its message's data. -/
theorem Frame.ofCall_inner_data (msg : Msg) :
    (Frame.ofCall msg).inner.data = msg.data := rfl

/-- `callMsg` installs its calldata argument as the message data. -/
theorem callMsg_data {sevm : Sevm} {parent : Devm} {gas : Nat} {value : B256}
    {caller target codeAddress : Adr} {stv isSt : Bool} {calldata : Bytes}
    {code : ByteArray} {dp : Bool} :
    (callMsg sevm parent gas value caller target codeAddress stv isSt
      calldata code dp).data = calldata := rfl

/-- A create frame's inner data is empty: `createMsg` sets `data := []` and
`processCreateMessage.msg` only re-bases the environment. -/
theorem Frame.ofCreate_inner_data_nil {sevm : Sevm} {devm : Devm}
    {createGas : Nat} {endowment : B256} {newAddress : Adr} {calldata : Bytes} :
    (Frame.ofCreate
      (createMsg sevm devm createGas endowment newAddress calldata)).inner.data
      = [] := rfl

/-- A spawned child has word-sized calldata before entry. CALL-family
inputs are memory slices sized by a popped word, and CREATE-family inputs
are empty. This also covers synchronous precompile entry. -/
theorem Xinst.step_spawn_inner_data_length_lt {sevm : Sevm} {pre : Devm}
    {x : Xinst} {f : Frame} {rsm : Resume}
    (hsg : sevm.benvStat.rules.stateGas = none)
    (hx : Xinst.step sevm pre x = .spawn f rsm) :
    f.inner.data.length < 2 ^ 256 := by
  cases x with
  | create =>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
    rw [hsg] at hx
    rcases eq1 : Devm.pop pre with _ | ⟨_, devm1⟩ <;> simp only [eq1] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq2 : Devm.popToNat devm1 with _ | ⟨_, devm2⟩ <;> simp only [eq2] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq3 : Devm.popToNat devm2 with _ | ⟨_, devm3⟩ <;> simp only [eq3] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    split at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    · simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
        Pure.pure, Except.pure] at hx
      repeat' split at hx
      all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hx
      all_goals obtain ⟨rfl, -⟩ := hx
      rw [Frame.ofCreate_inner_data_nil]
      decide
  | create2 =>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
    rw [hsg] at hx
    rcases eq1 : Devm.pop pre with _ | ⟨_, devm1⟩ <;> simp only [eq1] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq2 : Devm.popToNat devm1 with _ | ⟨_, devm2⟩ <;> simp only [eq2] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq3 : Devm.popToNat devm2 with _ | ⟨_, devm3⟩ <;> simp only [eq3] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq4 : Devm.pop devm3 with _ | ⟨_, devm4⟩ <;> simp only [eq4] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    split at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    · simp only [genericCreate.step, Bind.bind, Except.bind, Except.assert,
        Pure.pure, Except.pure] at hx
      repeat' split at hx
      all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hx
      all_goals obtain ⟨rfl, -⟩ := hx
      rw [Frame.ofCreate_inner_data_nil]
      decide
  | call =>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
    rw [hsg] at hx
    rcases eq1 : Devm.pop pre with _ | ⟨_, devm1⟩ <;> simp only [eq1] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq2 : Devm.popToAdr devm1 with _ | ⟨callee, devm2⟩ <;> simp only [eq2] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq3 : Devm.pop devm2 with _ | ⟨_, devm3⟩ <;> simp only [eq3] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq4 : Devm.popToNat devm3 with _ | ⟨_, devm4⟩ <;> simp only [eq4] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩
      <;> simp only [eq5] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    obtain ⟨w5, -, rfl⟩ := Devm.pop_of_popToNat_val eq5
    rcases eq6 : Devm.popToNat devm5 with _ | ⟨_, devm6⟩ <;> simp only [eq6] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq7 : Devm.popToNat devm6 with _ | ⟨_, devm7⟩ <;> simp only [eq7] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress devm7 callee) callee with ⟨_, _, _, _, _⟩
    simp only [hp11] at hx
    split at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    · simp only [genericCall.step, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at hx
      repeat' split at hx
      all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hx
      all_goals obtain ⟨rfl, -⟩ := hx
      all_goals
        rw [Frame.ofCall_inner_data, callMsg_data, Array.sliceD_length]
        exact B256.toNat_lt _
  | callcode =>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
    rw [hsg] at hx
    rcases eq1 : Devm.pop pre with _ | ⟨_, devm1⟩ <;> simp only [eq1] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq2 : Devm.popToAdr devm1 with _ | ⟨codeAddress, devm2⟩ <;> simp only [eq2] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq3 : Devm.pop devm2 with _ | ⟨_, devm3⟩ <;> simp only [eq3] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq4 : Devm.popToNat devm3 with _ | ⟨_, devm4⟩ <;> simp only [eq4] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq5 : Devm.popToNat devm4 with _ | ⟨inputSize, devm5⟩
      <;> simp only [eq5] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    obtain ⟨w5, -, rfl⟩ := Devm.pop_of_popToNat_val eq5
    rcases eq6 : Devm.popToNat devm5 with _ | ⟨_, devm6⟩ <;> simp only [eq6] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq7 : Devm.popToNat devm6 with _ | ⟨_, devm7⟩ <;> simp only [eq7] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress devm7 codeAddress) codeAddress with ⟨_, _, _, _, _⟩
    simp only [hp11] at hx
    split at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    · simp only [genericCall.step, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at hx
      repeat' split at hx
      all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hx
      all_goals obtain ⟨rfl, -⟩ := hx
      all_goals
        rw [Frame.ofCall_inner_data, callMsg_data, Array.sliceD_length]
        exact B256.toNat_lt _
  | delegatecall =>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
    rw [hsg] at hx
    rcases eq1 : Devm.pop pre with _ | ⟨_, devm1⟩ <;> simp only [eq1] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq2 : Devm.popToAdr devm1 with _ | ⟨codeAddress, devm2⟩ <;> simp only [eq2] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq3 : Devm.popToNat devm2 with _ | ⟨_, devm3⟩ <;> simp only [eq3] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputSize, devm4⟩
      <;> simp only [eq4] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    obtain ⟨w4, -, rfl⟩ := Devm.pop_of_popToNat_val eq4
    rcases eq5 : Devm.popToNat devm4 with _ | ⟨_, devm5⟩ <;> simp only [eq5] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq6 : Devm.popToNat devm5 with _ | ⟨_, devm6⟩ <;> simp only [eq6] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress devm6 codeAddress) codeAddress with ⟨_, _, _, _, _⟩
    simp only [hp11] at hx
    split at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    · simp only [genericCall.step, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at hx
      repeat' split at hx
      all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hx
      all_goals obtain ⟨rfl, -⟩ := hx
      all_goals
        rw [Frame.ofCall_inner_data, callMsg_data, Array.sliceD_length]
        exact B256.toNat_lt _
  | staticcall =>
    simp only [Xinst.step, Bind.bind, Except.bind, Except.assert] at hx
    rw [hsg] at hx
    rcases eq1 : Devm.pop pre with _ | ⟨_, devm1⟩ <;> simp only [eq1] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq2 : Devm.popToAdr devm1 with _ | ⟨target, devm2⟩ <;> simp only [eq2] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq3 : Devm.popToNat devm2 with _ | ⟨_, devm3⟩ <;> simp only [eq3] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq4 : Devm.popToNat devm3 with _ | ⟨inputSize, devm4⟩
      <;> simp only [eq4] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    obtain ⟨w4, -, rfl⟩ := Devm.pop_of_popToNat_val eq4
    rcases eq5 : Devm.popToNat devm4 with _ | ⟨_, devm5⟩ <;> simp only [eq5] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases eq6 : Devm.popToNat devm5 with _ | ⟨_, devm6⟩ <;> simp only [eq6] at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    rcases hp11 : sevm.benvStat.rules.gas.accessDelegation
        (addAccessedAddress devm6 target) target with ⟨_, _, _, _, _⟩
    simp only [hp11] at hx
    split at hx
    · simp only [XStep.ofExcept, reduceCtorEq] at hx
    · simp only [genericCall.step, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at hx
      repeat' split at hx
      all_goals simp only [XStep.ofExcept, XStep.spawn.injEq, reduceCtorEq] at hx
      all_goals obtain ⟨rfl, -⟩ := hx
      all_goals
        rw [Frame.ofCall_inner_data, callMsg_data, Array.sliceD_length]
        exact B256.toNat_lt _

/-- Every entered child of a covered-fork spawn has short calldata with a
covered fork: CALL-family children carry a memory slice sized by a popped
`B256.toNat`; CREATE-family children carry `[]`. -/
theorem Evm.step_spawn_child_data {pc : Nat} {sevm : Sevm} {pre : Devm}
    {f : Frame} {rsm : Resume} {pc' : Nat}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hs : Evm.step (⟨pc, sevm, pre⟩ : Evm) = .spawn f rsm pc')
    {cevm : Evm} (henter : f.enter = .run cevm) :
    cevm.sta.data.length < 2 ^ 256 ∧ CoveredFork cevm.sta.benvStat.fork := by
  obtain ⟨x, -, hx, -⟩ := Evm.step_spawn_inv hs
  constructor
  · rw [Frame.enter_data_eq henter]
    exact Xinst.step_spawn_inner_data_length_lt hfork.rules_stateGas_none hx
  · have hstat : cevm.sta.benvStat = sevm.benvStat := by
      rw [Frame.enter_run_benvStat henter, Xinst.step_spawn_benvStat hx]
    rw [hstat]
    exact hfork

/-- Every entered frame of a covered-fork execution has short calldata. -/
theorem Exec.rawFrameRoots_data_bound {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (hroot : sevm.data.length < 2 ^ 256)
    (hfork : CoveredFork sevm.benvStat.fork) :
    ∀ root ∈ Exec.rawFrameRoots run, root.sevm.data.length < 2 ^ 256 := by
  revert hroot hfork
  induction run with
  | halt hstep =>
      intro hroot hfork root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact hroot
  | cont hstep next ih =>
      intro hroot hfork root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact hroot
      · exact ih hroot hfork root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
        or_true])
  | doneErr hstep henter hresume =>
      intro hroot hfork root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.not_mem_nil, or_false] at member
      subst member
      exact hroot
  | doneOk hstep henter hresume next ih =>
      intro hroot hfork root member
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · exact hroot
      · exact ih hroot hfork root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
        or_true])
  | runErr hstep henter child hresume ih =>
      intro hroot hfork root member
      obtain ⟨hchild, hforkc⟩ := Evm.step_spawn_child_data hfork hstep henter
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | rfl | member
      · exact hroot
      · exact hchild
      · exact ih hchild hforkc root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
        or_true])
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro hroot hfork root member
      obtain ⟨hchild, hforkc⟩ := Evm.step_spawn_child_data hfork hstep henter
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | rfl | member | member
      · exact hroot
      · exact hchild
      · exact ihChild hchild hforkc root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
        or_true])
      · exact ihNext hroot hfork root (by simp only [Exec.rawFrameRoots, List.mem_cons, member,
        or_true])

/-! ## From retained slots to whole histories -/

/-- A retained slot whose frame message has short calldata enters only
short-calldata frames. -/
theorem RetainedXlot.rawFrames_data_bound
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hdata : frame.inner.data.length < 2 ^ 256)
    (hfork : CoveredFork frame.inner.benv.stat.fork) :
    ∀ root ∈ retained.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hdata' : sevm.data = frame.inner.data := by
        have e := Frame.enter_data_eq henter
        dsimp only at e
        exact e
      have hstat' : sevm.benvStat = frame.inner.benv.stat := by
        have e := Frame.enter_run_benvStat henter
        dsimp only at e
        exact e
      have hroot : sevm.data.length < 2 ^ 256 := by
        rw [hdata']
        exact hdata
      have hfork' : CoveredFork sevm.benvStat.fork := by
        rw [hstat']
        exact hfork
      exact Exec.rawFrameRoots_data_bound run hroot hfork'

/-- Call execution preserves the bound. -/
theorem ProcessMessageTrace.rawFrames_data_bound {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out)
    (hmsg : msg.data.length < 2 ^ 256) (hfork : CoveredFork msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 :=
  RetainedXlot.rawFrames_data_bound trace.retained trace.run hmsg hfork

/-- Create execution preserves the bound. -/
theorem ProcessCreateMessageTrace.rawFrames_data_bound {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out)
    (hmsg : msg.data.length < 2 ^ 256) (hfork : CoveredFork msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 :=
  RetainedXlot.rawFrames_data_bound trace.retained trace.run hmsg hfork

/-- A settled message call preserves the bound. -/
theorem MessageCallTrace.rawFrames_data_bound {msg : Msg} {state : State}
    {out : MsgCallOutput} (trace : MessageCallTrace msg state out)
    (hmsg : msg.data.length < 2 ^ 256) (hfork : CoveredFork msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  cases trace with
  | createCollision _ _ _ =>
      intro root hmem
      simp only [rawFrames, List.not_mem_nil] at hmem
  | createRun _ _ _ _ core _ =>
      intro root hmem
      simp only [MessageCallTrace.rawFrames] at hmem
      exact ProcessCreateMessageTrace.rawFrames_data_bound core hmsg hfork
        root hmem
  | callRun _ delegated refund hdel execMsg hexec _ _ core _ =>
      intro root hmem
      simp only [MessageCallTrace.rawFrames] at hmem
      have hdel_data := messageCallDelegation_data hdel
      have hdel_stat := messageCallDelegation_benvStat hdel
      have hexec_data : execMsg.data.length < 2 ^ 256 := by
        rw [hexec, messageCallExecutionMessage_data, hdel_data]
        exact hmsg
      have hexec_fork : CoveredFork execMsg.benv.stat.fork := by
        rw [hexec, messageCallExecutionMessage_benvStat, hdel_stat]
        exact hfork
      exact ProcessMessageTrace.rawFrames_data_bound core hexec_data hexec_fork
        root hmem

/-- `prepareMessage` copies `tx.data` (calls) or `[]` (creates). -/
theorem prepareMessage_data {benv : Benv} {tenv : Tenv} {tx : Tx} {msg : Msg}
    (h : prepareMessage benv tenv tx = .ok msg) :
    msg.data = tx.data ∨ msg.data = [] := by
  cases hrec : tx.type.receiver? with
  | none =>
    simp only [prepareMessage, hrec] at h
    cases h
    exact Or.inr rfl
  | some target =>
    simp only [prepareMessage, hrec] at h
    cases h
    exact Or.inl rfl

/-- A transaction's retained frames all have short calldata. -/
theorem TransactionTrace.rawFrames_data_bound {benv : Benv} {bout : BlockOutput}
    {tx : Tx} {index : Nat} {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork)
    (hgas : tx.gas ≤ benv.stat.blockGasLimit)
    (hlim : benv.stat.blockGasLimit < 2 ^ 63) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  have htx := TransactionTrace.data_length_lt trace hfork hgas hlim
  have hmsg : trace.msg.data.length < 2 ^ 256 := by
    rcases prepareMessage_data trace.prepared with h | h
    · rw [h]; exact htx
    · rw [h]; decide
  have hfork_msg : CoveredFork trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hfork
  intro root hmem
  simp only [TransactionTrace.rawFrames] at hmem
  exact MessageCallTrace.rawFrames_data_bound trace.message hmsg hfork_msg
    root hmem

/-- A system message's retained frames all have short calldata. -/
theorem SystemMessageTrace.rawFrames_data_bound {benv : Benv} {target : Adr}
    {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hdata : data.length < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  intro root hmem
  simp only [SystemMessageTrace.rawFrames] at hmem
  have hmsg : (systemTransactionMessage benv target data).data.length < 2 ^ 256 := by
    rw [systemTransactionMessage_data]
    exact hdata
  have hfork' : CoveredFork
      (systemTransactionMessage benv target data).benv.stat.fork := hfork
  exact MessageCallTrace.rawFrames_data_bound trace.message hmsg hfork'
    root hmem

/-- A transaction fold preserves the bound; each head's gas fits by its own
check, and `withState` preserves fork and gas limit definitionally. -/
theorem ApplyTransactionsTrace.rawFrames_data_bound
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork)
    (hlim : benv.stat.blockGasLimit < 2 ^ 63) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  revert trace hfork hlim
  induction txs generalizing benv bout finalBenv finalBout with
  | nil =>
      intro trace hfork hlim root hmem
      cases trace with
      | nil _ _ =>
        simp only [rawFrames, List.not_mem_nil] at hmem
  | cons head txs ih =>
      intro trace hfork hlim root hmem
      cases trace with
      | cons headTrace tailTrace =>
        rename_i index tx txState txBout
        simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · have hsg : benv.stat.rules.stateGas = none :=
            hfork.rules_stateGas_none
          have hsg_bt : (benv.beginTransaction).stat.rules.stateGas = none :=
            hsg
          have hgas : tx.gas ≤ benv.stat.blockGasLimit :=
            tx_gas_le_blockGasLimit_of_checked (benv := benv.beginTransaction)
              hsg_bt headTrace.checked
          exact TransactionTrace.rawFrames_data_bound headTrace hfork hgas
            hlim root hmem
        · exact ih tailTrace hfork hlim root hmem

/-- A block body's retained frames all have short calldata. -/
theorem AppliedBodyTrace.rawFrames_data_bound {benv : Benv}
    {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hfork : CoveredFork benv.stat.fork)
    (hlim : benv.stat.blockGasLimit < 2 ^ 63) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  intro root hmem
  simp only [AppliedBodyTrace.rawFrames, List.mem_append] at hmem
  rcases hmem with ((hmem | hmem) | hmem) | hmem
  · exact SystemMessageTrace.rawFrames_data_bound trace.beacon
      (systemData_length_lt (Or.inr ⟨_, rfl⟩)) hfork root hmem
  · exact SystemMessageTrace.rawFrames_data_bound trace.history
      (systemData_length_lt (Or.inr ⟨_, rfl⟩)) hfork root hmem
  · exact ApplyTransactionsTrace.rawFrames_data_bound trace.transactions
      hfork hlim root hmem
  · simp only [RequestsTrace.rawFrames, List.mem_append] at hmem
    have hst_tx := ApplyTransactionsTrace.stat_eq trace.transactions
    have hfork_req : CoveredFork trace.transactionBenv.stat.fork := by
      rw [hst_tx]
      exact hfork
    rcases hmem with hmem | hmem
    · exact SystemMessageTrace.rawFrames_data_bound trace.requests.withdrawal
        (systemData_length_lt (Or.inl rfl)) hfork_req root hmem
    · exact SystemMessageTrace.rawFrames_data_bound
        trace.requests.consolidation
        (systemData_length_lt (Or.inl rfl)) hfork_req root hmem

/-- A configured block's retained frames all have short calldata: the gas
limit comes from header validation, the fork from the block itself. -/
theorem ConfiguredBlockTrace.rawFrames_data_bound {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTrace cfg pre post) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  have hfork_benv : CoveredFork
      (initBenv trace.fork pre trace.block.header).stat.fork :=
    trace.covered
  have hlim : (initBenv trace.fork pre trace.block.header).stat.blockGasLimit
      < 2 ^ 63 :=
    trace.header_gasLimit_lt
  intro root hmem
  simp only [ConfiguredBlockTrace.rawFrames] at hmem
  exact AppliedBodyTrace.rawFrames_data_bound trace.bodyTrace hfork_benv hlim
    root hmem

/-- Every raw frame of a configured history has calldata shorter than
`2 ^ 256`, with no per-frame premise. -/
theorem ConfiguredHistoryTrace.calldata_bound {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, root.sevm.data.length < 2 ^ 256 := by
  induction trace with
  | refl _ _ _ =>
      intro root hmem
      simp only [rawFrames, List.not_mem_nil] at hmem
  | step prior block ih =>
      intro root hmem
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append] at hmem
      rcases hmem with hmem | hmem
      · exact ih root hmem
      · exact ConfiguredBlockTrace.rawFrames_data_bound block root hmem

/-- Admission corollary: the per-frame calldata premise used by the
configured-history headlines follows from the trace itself. -/
theorem ConfiguredHistoryTrace.frameAdmitted_calldata {cfg : ChainConfig}
    {checkpoint future : BlockChain} {ca : Adr}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.data.length < 2 ^ 256) := by
  rw [ConfiguredHistoryTrace.frameAdmitted_iff_rawFrames]
  intro root hmem _
  exact trace.calldata_bound root hmem

end ExecutionTrace

end Blanc

