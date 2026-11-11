import Blanc.Lift.ExactWalkCallChild

/-! An exact, fixed-width word writer. Its child result is supplied by an actual
execution law; the wrapper itself performs the CALL and its settlement. -/

namespace Blanc.Lift.SystemWordWriter

open Jaune

/-- Literal PUSH32/MSTORE followed by a zero-value CALL with the stored word as input. -/
def code (target : Adr) (word : B256) : ByteArray :=
  ⟨([0x7f] ++ word.toBytes ++ [0x5f, 0x52, 0x5f, 0x5f, 0x60, 0x20, 0x5f, 0x5f, 0x73] ++
    target.toBytes ++ [0x5a, 0xf1, 0x00]).toArray⟩

private def pushWord (word : B256) : Ninst :=
  .push word.toBytes (by rw [B256.length_toBytes])

private def pushTarget (target : Adr) : Ninst :=
  .push target.toBytes (by change 4 + 16 ≤ 32; decide)

def program (target : Adr) (word : B256) : Func :=
  .next (pushWord word) <| .next (.push [] (by decide)) <| .next (.reg .mstore) <|
  .next (.push [] (by decide)) <| .next (.push [] (by decide)) <|
  .next (.push [0x20] (by decide)) <| .next (.push [] (by decide)) <|
  .next (.push [] (by decide)) <| .next (pushTarget target) <|
  .next (.reg .gas) <| .next (.exec .call) <| .last .stop

theorem code_size (target : Adr) (word : B256) : (code target word).size = 65 := by
  simp only [code, ByteArray.size, List.size_toArray, List.length_append, B256.length_toBytes]
  rfl

theorem program_compile (target : Adr) (word : B256) :
    Func.compile [] 0 (program target word) = some (code target word).toList := by
  simp only [program, pushWord, pushTarget, Func.compile, Ninst.immAccepted, guard,
    ite_true, bind, Option.bind, pure, Ninst.toBytes, code, ByteArray.toList_eq_toList_data,
    pushToB8L, pushToB8, B256.length_toBytes,
    show target.toBytes.length = 20 from rfl, List.append_assoc]
  rfl

theorem program_noCalls (target : Adr) (word : B256) : (program target word).NoCalls := by
  trivial

/-- Memory after the writer's actual MSTORE. -/
def wordMemory (word : B256) : Mem := Mem.empty.write 0 word.toBytes

theorem target_word (target : Adr) : target.toBytes.toB256.toAdr = target := by
  have highZero : (target.1.toUInt64 >>> 32).toUInt32 = 0 := by
    rw [← UInt32.toNat_inj, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
    change (target.1.toNat >>> 32) % 4294967296 = 0
    rw [Nat.shiftRight_eq_zero _ _ (UInt32.toNat_lt target.1)]
  have roundtrip := B256.toB256_toBytes target.toB256
  have value : target.toBytes.toB256 = target.toB256 := by
    simpa only [Adr.toBytes, Adr.toB256, UInt32.toBytes, UInt16.toBytes,
      UInt32.toUInt8_toUInt16, List.cons_append, List.nil_append, B256.toBytes, B128.toBytes,
      UInt64.toBytes, UInt64.zero_shiftRight, UInt64.toUInt32_ofNat, UInt32.zero_shiftRight,
      UInt32.toUInt16_ofNat, UInt16.zero_shiftRight, UInt16.toUInt8_ofNat, highZero,
      UInt32.toUInt32_toUInt64, Bytes.toB256_zero_cons] using roundtrip
  rw [value, toAdr_toB256]

theorem prefix_run {sevm : Sevm} {base : Devm} {gas : Nat} (target : Adr) (word : B256)
    (fork : CoveredFork sevm.benvStat.fork) :
    ∀ {tail : Func} {post : Devm},
    Func.RunCompiled [] sevm
      (base.setMach ⟨[gas.toB256, target.toBytes.toB256, 0, 0, 32, 0, 0], wordMemory word,
        gas, base.stateGas⟩) tail post →
    Func.RunCompiled [] sevm
      (base.setMach ⟨[], .empty, gas + 27, base.stateGas⟩)
      (.next (pushWord word) <| .next (.push [] (by decide)) <| .next (.reg .mstore) <|
        .next (.push [] (by decide)) <| .next (.push [] (by decide)) <|
        .next (.push [0x20] (by decide)) <| .next (.push [] (by decide)) <|
        .next (.push [] (by decide)) <| .next (pushTarget target) <|
        .next (.reg .gas) tail) post := by
  intro tail post rest
  refine .next (Ninst.runCompiled_pushB256Full (w := word) (G := gas + 24) rfl
    (by change 0 < 1024; decide)) ?_
  dsimp only [pushTarget]
  func_run (9) [3]
  · exact Devm.extCost_empty_word
  · simp only [Nat.add_sub_cancel]
    exact rest

/-- Gas forwarded by the actual GAS/CALL pair after account access is charged. -/
def forwardedGas (base : Devm) (target : Adr) (gas : Nat) : Nat :=
  except64th (gas - accessCost target base.accessedAddresses)

/-- The parent's actual suspended state, including its prepaid input window. -/
def parent (base : Devm) (target : Adr) (word : B256) (gas : Nat) : Devm :=
  callSpawnParent
    (addAccessedAddress (base.setMach ⟨[], wordMemory word, gas, base.stateGas⟩) target)
    (forwardedGas base target gas + accessCost target base.accessedAddresses) 0 32 0 0

/-- The child message actually constructed by the writer's CALL. -/
def childMsg (sevm : Sevm) (base : Devm) (target : Adr) (word : B256)
    (gas : Nat) (childCode : ByteArray) : Msg :=
  callSpawnMsg sevm (parent base target word gas) (forwardedGas base target gas)
    target target 0 32 childCode false

/-- The successful child's settlement, followed by the writer's STOP. -/
def post (base : Devm) (target : Adr) (word : B256) (gas : Nat) (child : Devm) : Devm :=
  callChildPost (parent base target word gas) child 0 0

theorem parent_memory (base : Devm) (target : Adr) (word : B256) (gas : Nat) :
    (parent base target word gas).memory = wordMemory word := by
  change (wordMemory word).extends [(0, 32), (0, 0)] = wordMemory word
  apply Mem.extends_covered
  rw [show (wordMemory word).size = 32 from Mem.size_write_word]
  rfl

theorem childMsg_data (sevm : Sevm) (base : Devm) (target : Adr) (word : B256)
    (gas : Nat) (childCode : ByteArray) :
    (childMsg sevm base target word gas childCode).data = word.toBytes := by
  change (parent base target word gas).memory.data.sliceD 0 32 0 = _
  rw [parent_memory]
  exact Mem.read_write_word

/-- The wrapper crosses the real CALL, using only the execution of the child message it built. -/
theorem call_run {sevm : Sevm} {base child : Devm} {target : Adr} {word : B256}
    {gas : Nat} {childCode : ByteArray}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (gasLt : gas < 2 ^ 256) (affordable : accessCost target base.accessedAddresses ≤ gas)
    (installed : base.getCode target = childCode)
    (nondelegated : getDelegatedCodeAddress childCode = none)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target = false)
    (childRun : exec (initEvm (childMsg sevm base target word gas childCode)) = .ok child)
    (childError : child.error = none) :
    Ninst.RunCompiled sevm
      (base.setMach ⟨[gas.toB256, target.toBytes.toB256, 0, 0, 32, 0, 0], wordMemory word,
        gas, base.stateGas⟩) (.exec .call) (post base target word gas child) := by
  let d := base.setMach ⟨[], wordMemory word, gas, base.stateGas⟩
  have hdel : accessDelegation (addAccessedAddress d target) target =
      (false, target, childCode, 0, addAccessedAddress d target) := by
    unfold accessDelegation
    change (match getDelegatedCodeAddress (base.getCode target) with
      | some adr => _ | none => _) = _
    rw [installed, nondelegated]
    change (false, target, base.getCode target, 0, addAccessedAddress d target) = _
    rw [installed]
  have hext : d.extCost [(0, 32), (0, 0)] = 0 := by
    apply Devm.extCost_covered
    rw [show (wordMemory word).size = 32 from Mem.size_write_word]
    rfl
  have splitGas : calculateMsgCallGas 0 gas.toB256.toNat gas 0
      (accessCost target base.accessedAddresses + 0) =
      (forwardedGas base target gas + accessCost target base.accessedAddresses,
        forwardedGas base target gas) := by
    rw [calculateMsgCallGas_zero (by omega), B256.toNat_toB256_of_lt gasLt]
    simp only [Nat.sub_zero, Nat.add_zero]
    have bounded : forwardedGas base target gas ≤ gas := by
      unfold forwardedGas except64th
      omega
    rw [show min gas (except64th (gas - accessCost target base.accessedAddresses)) =
      forwardedGas base target gas from Nat.min_eq_right bounded]
  have hsub : (addAccessedAddress d target).state.subBal sevm.currentTarget 0 =
      some (base.state.setBal sevm.currentTarget (base.state.bal sevm.currentTarget - 0)) := by
    change base.state.subBal sevm.currentTarget 0 = _
    unfold State.subBal
    rw [ite_eq_right (by exact B256.not_lt.mpr (B256.zero_le _))]
  have run := Ninst.runCompiled_call_zero_child
    (devm := base.setMach ⟨[gas.toB256, target.toBytes.toB256, 0, 0, 32, 0, 0],
      wordMemory word, gas, base.stateGas⟩)
    (s := []) (dp := false) (dadr := target) (code := childCode) (dgc := 0)
    (d1 := addAccessedAddress d target) (ext := 0)
    (acc := accessCost target base.accessedAddresses + 0)
    (mcc := forwardedGas base target gas + accessCost target base.accessedAddresses)
    (mcs := forwardedGas base target gas)
    fork rfl ?_ ?_ ?_ splitGas ?_ depth nonprecompile (by decide) hsub ?_ childError
  · exact run
  · exact hext
  · rw [target_word]
    exact hdel
  · rw [target_word]
    rfl
  · change forwardedGas base target gas + accessCost target base.accessedAddresses + 0 ≤ gas
    unfold forwardedGas except64th
    omega
  · rw [target_word]
    exact childRun

/-- Original successful execution of the exact writer runtime. No child success is assumed
independently of the actual child execution equation. -/
theorem exec {sevm : Sevm} {base child : Devm} {target : Adr} {word : B256}
    {gas : Nat} {childCode : ByteArray}
    (fork : CoveredFork sevm.benvStat.fork) (depth : sevm.depth ≠ 0)
    (gasLt : gas < 2 ^ 256) (affordable : accessCost target base.accessedAddresses ≤ gas)
    (installed : base.getCode target = childCode)
    (nondelegated : getDelegatedCodeAddress childCode = none)
    (nonprecompile : sevm.benvStat.rules.isPrecomp target = false)
    (runtime : sevm.code = code target word)
    (childRun : Jaune.exec (initEvm (childMsg sevm base target word gas childCode)) = .ok child)
    (childError : child.error = none) :
    Jaune.exec ⟨0, sevm, base.setMach ⟨[], .empty, gas + 27, base.stateGas⟩⟩ =
      .ok (post base target word gas child) := by
  have run := call_run fork depth gasLt affordable installed nondelegated nonprecompile childRun childError
  have full : Func.RunCompiled [] sevm
      (base.setMach ⟨[], .empty, gas + 27, base.stateGas⟩)
      (program target word) (post base target word gas child) :=
    prefix_run target word fork (.next run (.last rfl))
  exact Func.exec_of_runCompiled_prefix full (program_noCalls target word)
    (program_compile target word) (by rw [runtime, List.append_nil])

/-- The settled state exposes all fields used by transaction and receipt forwarding.
In particular the CALL succeeds with status one; STOP does not hide a failed child. -/
theorem post_facts (base child : Devm) (target : Adr) (word : B256) (gas : Nat)
    (noOutput : child.output = []) :
    (post base target word gas child).state = child.state ∧
    (post base target word gas child).logs = base.logs ++ child.logs ∧
    (post base target word gas child).refundCounter = base.refundCounter + child.refundCounter ∧
    (post base target word gas child).error = base.error ∧
    (post base target word gas child).output = base.output ∧
    (post base target word gas child).accountsToDelete = base.accountsToDelete.union child.accountsToDelete ∧
    (post base target word gas child).returnData = [] ∧
    (post base target word gas child).memory = wordMemory word ∧
    (post base target word gas child).stack = [1] := by
  rcases callChildPost_facts (parent base target word gas) child 0 0 noOutput with
    ⟨stack, memory, _, state, _, logs, refund, error, output, returnData, deletions, _, _, _⟩
  refine ⟨state, logs, refund, error, output, deletions, returnData, ?_, stack⟩
  exact memory.trans (parent_memory base target word gas)

theorem post_code (base child : Devm) (target : Adr) (word : B256) (gas : Nat) (a : Adr) :
    (post base target word gas child).getCode a = child.getCode a := rfl

theorem post_storage (base child : Devm) (target : Adr) (word : B256) (gas : Nat) (a : Adr) :
    (post base target word gas child).getStor a = child.getStor a := rfl

end Blanc.Lift.SystemWordWriter
