import Blanc.Lift.Usdc.ModernCallerReach

/-! Actual modern removeMinter write keys, ordered hash provenance and same-cell nonincrease. -/
namespace Blanc.Lift.Usdc.ModernRemoveMinterReach

open Jaune Blanc Blanc.Lift

def core : ModernVersion → SFunc
  | .v2 => ImplV2.t_16cb_c55
  | .v2_1 => ImplV2_1.t_1641_c55
  | .v2_2 => Impl.t_192e_c65

/-- A removeMinter store retains both its nonincrease bound and an actual
successful hash of the exact minter/allowance mapping preimage. -/
def StoreSource (Q : Sevm → Devm → Ninst → Devm → Prop)
    (observe : Conf → Conf → Prop) (sevm : Sevm) (T : Conf) : Prop :=
  ∃ key value rest, T.d.stack = key :: value :: rest ∧
    value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat ∧
    ∃ (account : Adr) (base : B256), (base = 12 ∨ base = 13) ∧
      key = mapSlot account.toB256 base ∧
      ObservedKeccak Q observe sevm (account.toB256.toBytes ++ base.toBytes) (fun _ => True)

/-- The flag write clears bits of its same-key reload; the allowance write stores zero.
Neither case needs distinct hash outputs or a successful enclosing frame. -/
theorem core_source {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {arg : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (0 :: arg :: S) M G, core version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    StoreSource Q observe sevm T := by
  cases version
  all_goals
    simp only [core] at run
    first
    | unfold ImplV2.t_16cb_c55 at run
    | unfold ImplV2_1.t_1641_c55 at run
    | unfold Impl.t_192e_c65 at run
    orsd
    iterate 3 orsx
    rw [show Bytes.toB256 [0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,
      0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff,0xff] = ff20 from rfl,
      B256.and_comm arg ff20, ff20_and_word] at run
    iterate 12 orsx
    obtain ⟨_, flagHash, run⟩ := ObservedKeccak.of_next erase run hT
      (input := arg.toAdr.toB256.toBytes ++ (12 : B256).toBytes)
      (shape := fun _ => True)
      (by exact Mem.read_two_word_writes_at_raw _ 0 _ _) (by trivial)
    simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl,
      show (Bytes.toB256 [32]).toNat = 32 from rfl] at run
    rw [Mem.read_two_word_writes_at_raw] at run
    orsx
    obtain ⟨loadedPost, loadStep, run⟩ := ObservedReach.rs_next run hT
    have loadRun := erase loadStep
    obtain ⟨key, rest, pop, push⟩ := of_run_sload loadRun
    simp only [Stack.Pop, Stack.Push, Split, St.stack, List.cons_append, List.nil_append,
      List.cons.injEq] at pop push
    obtain ⟨rfl, rfl⟩ := pop
    have storage := fun k => Devm.getStorVal_of_state (of_run_sload_state loadRun)
      sevm.currentTarget k
    simp only [St.getStorVal] at storage
    rw [St.self push (SolcStorageReturn.sload_memory loadRun), St.getStorVal, storage] at run
    simp only [St.memory] at run
    iterate 3 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · refine ⟨_, _, _, rfl, ?_, arg.toAdr, 12, .inl rfl, rfl, flagHash⟩
      simp only [St.getStorVal, B256.toNat_and]
      exact Nat.and_le_right
    obtain ⟨b', G1, rfl⟩ := SolcStorageReturn.ri_sstore_any (erase step)
    iterate 6 orsx
    have readAllowance :
        (((((M.write 0 arg.toAdr.toB256.toBytes).write 32 (12 : B256).toBytes).read
          0 64).2.write 32 (13 : B256).toBytes).read 0 64).1 =
          arg.toAdr.toB256.toBytes ++ (13 : B256).toBytes := by
      apply Mem.read_after_right_write
      intro i hi
      have ha : arg.toAdr.toB256.toBytes ≠ [] := by
        intro equal
        have length := B256.length_toBytes arg.toAdr.toB256
        simp only [equal, List.length_nil, OfNat.zero_ne_ofNat] at length
      have hb : (12 : B256).toBytes ≠ [] := by decide
      show ((M.write 0 arg.toAdr.toB256.toBytes).write 32 (12 : B256).toBytes).data.getD i 0 = _
      rw [Mem.getD_write_below_end _ 32 hb (by simp only [B256.length_toBytes]; omega),
        ite_eq_right (by omega),
        Mem.getD_write_below_end _ 0 ha (by simp only [B256.length_toBytes]; omega),
        ite_eq_left (by omega), Nat.sub_zero]
    obtain ⟨_, allowanceHash, run⟩ := ObservedKeccak.of_next erase run hT
      (input := arg.toAdr.toB256.toBytes ++ (13 : B256).toBytes)
      (shape := fun _ => True) readAllowance (by trivial)
    simp only [show (Bytes.toB256 [32]).toNat = 32 from rfl,
      show Bytes.toB256 [12] = (12 : B256) from rfl,
      show Bytes.toB256 [13] = (13 : B256) from rfl] at run
    rw [readAllowance] at run
    iterate 2 orsx
    rcases ObservedReach.sstoreS run with rfl | ⟨d', step, _, run⟩
    · exact ⟨_, _, _, rfl, Nat.zero_le _, arg.toAdr, 13, .inr rfl, rfl, allowanceHash⟩
    exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim

/-- The flag write clears bits of its same-key reload; the allowance write stores zero.
Neither case needs distinct hash outputs or a successful enclosing frame. -/
theorem core_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {arg : B256} {S : List B256}
    {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (0 :: arg :: S) M G, core version, K⟩ T)
    (hT : AtSstore T) (cont : ∀ f ∈ K, f.sstoreFreeIn [] = true) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := core_source erase run hT cont
  exact ⟨key, value, rest, stack, bound⟩

def wrapper : ModernVersion → SFunc
  | .v2 => ImplV2.t_04e8_c143
  | .v2_1 => ImplV2_1.t_04fd_c139
  | .v2_2 => Impl.t_0534_c172

def stop : ModernVersion → SFunc
  | .v2 => ImplV2.t_0407_c143
  | .v2_1 => ImplV2_1.t_03f1_c139
  | .v2_2 => Impl.t_0428_c172

/-- ABI bounds and the master-minter guard lead to the same non-increasing stores. -/
theorem wrapper_source {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (selector :: S) M G, wrapper version, []⟩ T) (hT : AtSstore T) :
    StoreSource Q observe sevm T := by
  have cont : ∀ f ∈ [stop version], f.sstoreFreeIn [] = true := by
    intro f member
    have same := List.mem_singleton.mp member
    subst f
    cases version <;> decide +kernel
  cases version
  all_goals
    simp only [wrapper] at run
    first
    | unfold ImplV2.t_04e8_c143 at run
    | unfold ImplV2_1.t_04fd_c139 at run
    | unfold Impl.t_0534_c172 at run
    orsd
    iterate 10 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_04fe_c143 at run
    | unfold ImplV2_1.t_0513_c139 at run
    | unfold Impl.t_054a_c172 at run
    orsd
    iterate 5 orsx
    obtain ⟨g, _, hg, run⟩ := ObservedReach.rs_callIn run hT
    first
    | change some ImplV2.t_1658_c55 = some g at hg
    | change some ImplV2_1.t_15ce_c55 = some g at hg
    | change some Impl.t_18bb_c65 = some g at hg
    cases hg
    first
    | unfold ImplV2.t_1658_c55 at run
    | unfold ImplV2_1.t_15ce_c55 at run
    | unfold Impl.t_18bb_c65 at run
    orsd
    orsx
    orsld
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel) cont).elim
    first
    | exact core_source (version := .v2) erase run hT cont
    | exact core_source (version := .v2_1) erase run hT cont
    | exact core_source (version := .v2_2) erase run hT cont

/-- Compatibility projection of the stronger source law. -/
theorem wrapper_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {selector : B256}
    {M : Mem} {G : Nat} {T : Conf}
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b (selector :: S) M G, wrapper version, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := wrapper_source erase run hT
  exact ⟨key, value, rest, stack, bound⟩

def entry : ModernVersion → Nat
  | .v2 => 143
  | .v2_1 => 139
  | .v2_2 => 172

/-- The original entry and selector dispatcher reach only the removeMinter wrapper. -/
theorem reach_source {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x3092afd5)
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b S M G, ModernCallerReach.start version, []⟩ T) (hT : AtSstore T) :
    StoreSource Q observe sevm T := by
  have routing : SFunc.selWalk (Blanc.Sevm.selector sevm) (ModernCallerReach.dispatch version) =
      .inl (Blanc.Sevm.selector sevm, entry version) := by
    rw [selected]
    cases version <;> decide +kernel
  have wrapperAt : version.cert.prog[entry version]? = some (wrapper version) := by
    cases version <;> rfl
  have word : Sevm.dataWord sevm (Bytes.toB256 [0]) >>> (Bytes.toB256 [0xe0]).toNat =
      Blanc.Sevm.selector sevm := rfl
  cases version
  all_goals
    simp only [ModernCallerReach.start] at run
    first
    | unfold ImplV2.t_0000_c0 at run
    | unfold ImplV2_1.t_0000_c0 at run
    | unfold Impl.t_0000_c0 at run
    iterate 7 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_0010_c0 at run
    | unfold ImplV2_1.t_0010_c0 at run
    | unfold Impl.t_0010_c0 at run
    orsd
    iterate 5 orsx
    rcases ObservedReach.rs_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
    swap
    · exact (Reach.false_of_sstoreFree (E := []) rfl run.forget hT (by decide +kernel)
        (fun _ h => by cases h)).elim
    first
    | unfold ImplV2.t_001a_c0 at run
    | unfold ImplV2_1.t_001a_c0 at run
    | unfold Impl.t_001a_c0 at run
    iterate 4 orsx
    rw [word] at run
    obtain ⟨-, g, _, hg, run⟩ := ObservedReach.selWalk_inlS erase routing run hT
    rw [wrapperAt] at hg
    cases hg
    first
    | exact wrapper_source (version := .v2) erase run hT
    | exact wrapper_source (version := .v2_1) erase run hT
    | exact wrapper_source (version := .v2_2) erase run hT

/-- Compatibility projection of the stronger source law. -/
theorem reach_nonInc {version : ModernVersion}
    {Q : Sevm → Devm → Ninst → Devm → Prop} {observe : Conf → Conf → Prop}
    (erase : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {T : Conf}
    (selected : Blanc.Sevm.selector sevm = 0x3092afd5)
    (run : ObservedReach Q observe version.cert.prog sevm
      ⟨St b S M G, ModernCallerReach.start version, []⟩ T) (hT : AtSstore T) :
    ∃ key value rest, T.d.stack = key :: value :: rest ∧
      value.toNat ≤ (T.d.getStorVal sevm.currentTarget key).toNat := by
  obtain ⟨key, value, rest, stack, bound, _⟩ := reach_source erase selected run hT
  exact ⟨key, value, rest, stack, bound⟩

/-- Every original successful removeMinter store is bounded by its own pre-state cell. -/
theorem successfulSstore_source (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat ∧
      ∃ (account : Adr) (base : B256), (base = 12 ∨ base = 13) ∧
        write.key = mapSlot account.toB256 base ∧
        ∃ hashPc, KeccakBefore root node (account.toB256.toBytes ++ base.toBytes) hashPc := by
  obtain ⟨decoded, rest, stack⟩ := Exec.Deriv.successfulSstore?_decoded found
  obtain ⟨κ, reach, ok⟩ :=
    observed_reach_of_parentPrefix_noStateGas version.cert_check pc code hsg chain
  obtain ⟨g, tree, -⟩ := ok.tree_of_sstore decoded
  have target : AtSstore (κ.conf node.devm) := ⟨g, tree⟩
  have begin : (Cursor.start version.cert).conf root.devm =
      ⟨root.devm, ModernCallerReach.start version, []⟩ := by
    cases version <;> rfl
  rw [begin, St.self' root.devm] at reach
  obtain ⟨key, value, other, shape, bound, account, base, bases, slot, hash⟩ :=
    reach_source (fun h => StepIn.toRun h) selected reach target
  have same := List.cons.inj (stack.symm.trans shape)
  have keyEq := same.1
  have valueEq := (List.cons.inj same.2).1
  rw [← keyEq, ← valueEq] at bound
  rw [← Exec.Deriv.ParentPrefix.sevm_eq chain] at bound
  obtain ⟨occurrence, next, here, instruction, success, before, edge, after,
    _, _, hashStack, input⟩ := hash.actual
  exact ⟨bound, account, base, bases, keyEq.trans slot, occurrence.node.pc,
    occurrence, next, rfl, instruction, success, before, edge, after, hashStack, input⟩

/-- Compatibility projection of the stronger original-store source law. -/
theorem successfulSstore_nonInc (version : ModernVersion) {root node : Exec.Deriv}
    (pc : root.pc = 0) (code : root.sevm.code = version.code)
    (hsg : root.sevm.benvStat.rules.stateGas = none)
    (chain : Exec.Deriv.ParentPrefix root node)
    (selected : Blanc.Sevm.selector root.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  exact (successfulSstore_source version pc code hsg chain selected found).1

end Blanc.Lift.Usdc.ModernRemoveMinterReach

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Raw-history membership supplies the original entry for the same-node nonincrease law. -/
theorem ConfiguredHistoryTraceIn.modernRemoveMinter_nonInc
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {version : ModernVersion} {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.value.toNat ≤ (node.devm.getStorVal node.sevm.currentTarget write.key).toNat := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = version.code := by rw [← same]; exact code
  have rootSelected : Sevm.selector root.sevm = 0x3092afd5 := by rw [← same]; exact selected
  exact ModernRemoveMinterReach.successfulSstore_nonInc version pc rootCode hsg chain rootSelected found

/-- Every removeMinter store is tied to a successful original slot12/slot13
hash before that same store, including frames whose final outcome reverts. -/
theorem ConfiguredHistoryTraceIn.modernRemoveMinter_write_source
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {version : ModernVersion} {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ root ∈ history.rawFrames, Exec.Deriv.ParentPrefix root node ∧
      root.sevm.code = version.code ∧ Sevm.selector root.sevm = 0x3092afd5 ∧
      ∃ (account : Adr) (base : B256), (base = 12 ∨ base = 13) ∧
        write.key = mapSlot account.toB256 base ∧
        ∃ hashPc, KeccakBefore root node (account.toB256.toBytes ++ base.toBytes) hashPc := by
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp member
  obtain ⟨pc, -, hsg, -, -⟩ := history.rawFrame_entryFacts capabilities root inFrames
  have same := Exec.Deriv.ParentPrefix.sevm_eq chain
  have rootCode : root.sevm.code = version.code := by rw [← same]; exact code
  have rootSelected : Sevm.selector root.sevm = 0x3092afd5 := by rw [← same]; exact selected
  exact ⟨root, inFrames, chain, rootCode, rootSelected,
    (ModernRemoveMinterReach.successfulSstore_source version pc rootCode hsg chain rootSelected found).2⟩

section RemoveHashKeys

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  {version : ModernVersion} {P : Adr}

/-- Decode only the two canonical mapping preimages used by modern removeMinter.
The address comes from the input bytes, never from a comparison of digests. -/
def modernRemoveInputKey? (input : Bytes) : Option HistoricalMappingKey :=
  let account := (Bytes.toB256 (input.take 32)).toAdr
  if input = account.toB256.toBytes ++ (12 : B256).toBytes then
    some (.modern (.minter account))
  else if input = account.toB256.toBytes ++ (13 : B256).toBytes then
    some (.modern (.minterAllowance account))
  else none

theorem modernRemoveInputKey?_complete (account : Adr) (base : B256)
    (minterBase : base = 12 ∨ base = 13) :
    ∃ key, modernRemoveInputKey? (account.toB256.toBytes ++ base.toBytes) = some key ∧
      key.slot = mapSlot account.toB256 base := by
  have address : (Bytes.toB256 ((account.toB256.toBytes ++ base.toBytes).take 32)).toAdr = account := by
    rw [List.take_length_append' (B256.length_toBytes _).symm,
      B256.toB256_toBytes, toAdr_toB256]
  unfold modernRemoveInputKey?
  dsimp only
  rw [address]
  rcases minterBase with rfl | rfl
  · exact ⟨.modern (.minter account), ite_eq_left rfl, rfl⟩
  · have different : account.toB256.toBytes ++ (13 : B256).toBytes ≠
        account.toB256.toBytes ++ (12 : B256).toBytes := by
      intro equal
      have words := congrArg Bytes.toB256 (List.append_cancel_left equal)
      simp only [B256.toB256_toBytes] at words
      exact (by decide : (13 : B256) ≠ 12) words
    exact ⟨.modern (.minterAllowance account), by rw [ite_eq_right different, ite_eq_left rfl], rfl⟩

theorem modernRemoveInputKey?_sound {input : Bytes} {key : HistoricalMappingKey}
    (recognized : modernRemoveInputKey? input = some key) :
    ∃ (account : Adr) (base : B256), (base = 12 ∨ base = 13) ∧
      input = account.toB256.toBytes ++ base.toBytes ∧ key.slot = mapSlot account.toB256 base := by
  unfold modernRemoveInputKey? at recognized
  dsimp only at recognized
  split at recognized
  next at12 => cases recognized; exact ⟨_, 12, .inl rfl, at12, rfl⟩
  next =>
    split at recognized
    next at13 => cases recognized; exact ⟨_, 13, .inr rfl, at13, rfl⟩
    next => cases recognized

/-- Successful original hash inputs in the removeMinter selector, including inputs
whose subsequent writes clear a slot. No unexecuted calldata row is collected. -/
def modernRemoveHashKey? (version : ModernVersion) (P : Adr) (node : Exec.Deriv) : Option HistoricalMappingKey :=
  if node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm = 0x3092afd5 ∧
      node.devm.stack.take 2 = [0, 64] then
    match node.sevm.code.getInst node.pc with
    | some (.next (.reg .keccak256)) =>
        match Rinst.run ⟨node.pc, node.sevm, node.devm⟩ .keccak256 with
        | .ok _ => modernRemoveInputKey? (node.devm.memory.read 0 64).1
        | .error _ => none
    | _ => none
  else none

def actualModernRemoveHashKeys (version : ModernVersion) (P : Adr)
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) : List HistoricalMappingKey :=
  history.rawNodes.filterMap (modernRemoveHashKey? version P)

theorem modernRemoveHashKey?_complete {P : Adr} {root : Exec.Deriv}
    (occurrence : Exec.NinstOccurrence root) {post : Devm}
    (target : occurrence.node.sevm.currentTarget = P)
    (code : occurrence.node.sevm.code = version.code)
    (selected : Sevm.selector occurrence.node.sevm = 0x3092afd5)
    (instruction : occurrence.instruction = .reg .keccak256)
    (success : occurrence.stepResult = .ok post)
    (stack : ∃ rest, occurrence.node.devm.stack = 0 :: 64 :: rest)
    {input : Bytes} (read : (occurrence.node.devm.memory.read 0 64).1 = input)
    {key : HistoricalMappingKey} (recognized : modernRemoveInputKey? input = some key) :
    modernRemoveHashKey? version P occurrence.node = some key := by
  have decoded := occurrence.decoded
  rw [instruction] at decoded
  have run := occurrence.stepRun
  rw [instruction, success] at run
  simp only [Ninst.StepRun, Ninst.step_reg] at run
  have executed := (Step.run_ofExecution.mp run).2.symm
  obtain ⟨rest, stack⟩ := stack
  have shape : occurrence.node.devm.stack.take 2 = [0, 64] := by
    rw [stack]; rfl
  rw [modernRemoveHashKey?, ite_eq_left ⟨target, code, selected, shape⟩,
    decoded, executed, read]
  exact recognized


theorem modernRemoveHashKey?_sound {P : Adr} {node : Exec.Deriv}
    {key : HistoricalMappingKey} (recognized : modernRemoveHashKey? version P node = some key) :
    node.sevm.currentTarget = P ∧ node.sevm.code = version.code ∧
      Sevm.selector node.sevm = 0x3092afd5 ∧
      Ninst.At node.sevm.code node.pc (.reg .keccak256) ∧
      node.devm.stack.take 2 = [0, 64] ∧ ∃ post,
        Rinst.run ⟨node.pc, node.sevm, node.devm⟩ .keccak256 = .ok post ∧
        modernRemoveInputKey? (node.devm.memory.read 0 64).1 = some key := by
  unfold modernRemoveHashKey? at recognized
  split at recognized
  next scope =>
    split at recognized
    next decoded =>
      split at recognized
      next post executed =>
        exact ⟨scope.1, scope.2.1, scope.2.2.1, decoded, scope.2.2.2,
          post, executed, recognized⟩
      next => cases recognized
    next => cases recognized
  next => cases recognized

/-- Every collected key has its successful original hash occurrence and exact
canonical input, even if the enclosing frame later reverts. -/
theorem ConfiguredHistoryTraceIn.actualModernRemoveHashKeys_sound
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    {key : HistoricalMappingKey} (member : key ∈ actualModernRemoveHashKeys version P history) :
    ∃ root ∈ history.rawFrames, ∃ occurrence : Exec.NinstOccurrence root,
      occurrence.node ∈ history.rawNodes ∧ occurrence.node.sevm.currentTarget = P ∧
      occurrence.node.sevm.code = version.code ∧
      Sevm.selector occurrence.node.sevm = 0x3092afd5 ∧
      occurrence.node.devm.stack.take 2 = [0, 64] ∧
      occurrence.instruction = .reg .keccak256 ∧ ∃ post,
        occurrence.stepResult = .ok post ∧ ∃ (account : Adr) (base : B256),
          (base = 12 ∨ base = 13) ∧
          (occurrence.node.devm.memory.read 0 64).1 = account.toB256.toBytes ++ base.toBytes ∧
          key.slot = mapSlot account.toB256 base := by
  obtain ⟨node, inNodes, recognized⟩ := List.mem_filterMap.mp member
  obtain ⟨target, code, selected, decoded, shape, post, executed, input⟩ :=
    modernRemoveHashKey?_sound recognized
  obtain ⟨root, inFrames, chain⟩ :=
    (history.mem_rawNodes_iff_rawFrame_parentPrefix node).mp inNodes
  have reached : node ∈ Exec.rawNodes root.exc := by
    obtain ⟨earlier, decomposition⟩ := Exec.Deriv.ParentPrefix.rawNodes_decomposition chain
    rw [decomposition]
    exact List.mem_append_right earlier (Exec.mem_rawNodes_self node.exc)
  obtain ⟨occurrence, same, instruction⟩ :=
    Exec.exists_ninstOccurrence_of_mem_rawNodes reached decoded
  have step : Ninst.StepRun occurrence.node.pc occurrence.node.sevm occurrence.node.devm
      occurrence.instruction .none (.ok post) := by
    rw [same, instruction]
    simp only [Ninst.StepRun, Ninst.step_reg]
    exact Step.run_ofExecution.mpr ⟨rfl, executed.symm⟩
  have success := (occurrence_stepRun_unique occurrence (slot := .none) trivial step).2
  obtain ⟨account, base, minterBase, read, slot⟩ := modernRemoveInputKey?_sound input
  refine ⟨root, inFrames, occurrence, ?_⟩
  rw [same]
  exact ⟨inNodes, target, code, selected, shape, instruction, post, success,
    account, base, minterBase, read, slot⟩

/-- Every removeMinter write has a key collected at its original successful hash. -/
theorem ConfiguredHistoryTraceIn.modernRemoveMinter_write_collected
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {node : Exec.Deriv}
    (member : node ∈ history.rawNodes) (target : node.sevm.currentTarget = P)
    (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    ∃ key ∈ actualModernRemoveHashKeys version P history, write.key = key.slot := by
  obtain ⟨root, inFrames, chain, code, selected, account, base, bases, slot, pc, source⟩ :=
    ConfiguredHistoryTraceIn.modernRemoveMinter_write_source history capabilities member code selected found
  obtain ⟨occurrence, next, _, instruction, success, before, _, _, stack, read⟩ := source
  have same := Exec.Deriv.ParentPrefix.sevm_eq before
  have targetRoot : root.sevm.currentTarget = P := by
    rw [← Exec.Deriv.ParentPrefix.sevm_eq chain]
    exact target
  have inNodes := (history.mem_rawNodes_iff_rawFrame_parentPrefix occurrence.node).mpr
    ⟨root, inFrames, before⟩
  obtain ⟨key, recognized, keySlot⟩ := modernRemoveInputKey?_complete account base bases
  have collected := modernRemoveHashKey?_complete (P := P) (version := version) occurrence
    (by rw [same]; exact targetRoot) (by rw [same]; exact code)
    (by rw [same]; exact selected) instruction success stack read recognized
  exact ⟨key, List.mem_filterMap.mpr ⟨occurrence.node, inNodes, collected⟩,
    slot.trans keySlot.symm⟩

/-- Actual minter mapping-hash freshness excludes the implementation slot for
every removeMinter write, including both flag masking and zero allowance stores. -/
theorem ConfiguredHistoryTraceIn.modernRemoveMinter_write_ne_implSlot
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) {initial : HistoricalMappingKey → Prop}
    (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
    (fresh : SlotFootprint.FreshKeys HistoricalMappingKey.slot fixedSlots initial
      (actualModernRemoveHashKeys version P history))
    {node : Exec.Deriv} (member : node ∈ history.rawNodes)
    (target : node.sevm.currentTarget = P) (code : node.sevm.code = version.code)
    (selected : Sevm.selector node.sevm = 0x3092afd5)
    {write : Exec.StorageWrite} (found : Exec.Deriv.successfulSstore? node = some write) :
    write.key ≠ implSlot := by
  obtain ⟨key, collected, slot⟩ :=
    ConfiguredHistoryTraceIn.modernRemoveMinter_write_collected history capabilities
      member target code selected found
  rw [slot]
  exact HistoricalMappingKey.slot_ne_implSlot initialApart fresh collected

end RemoveHashKeys

end Blanc.Lift.Usdc
