import Blanc.Lift.UniswapV2Pair.MutableTurns
import Blanc.Lift.UniswapV2Pair.PairSelectors
import Blanc.Lift.UniswapV2Pair.PairLockedEntries
import Blanc.Lift.UniswapV2Pair.PermitTurns
import Blanc.Lift.UniswapV2Pair.TransferFromSource
import Blanc.Lift.UniswapV2Pair.InitializeSource
import Blanc.Lift.UniswapV2Pair.StaticViewSource

/-!
# The Pair-frame supply while the Pair is locked

While the Pair's lock is held, a committed Pair frame is one of the entries that do not
take the lock: transfer, approve, transferFrom, permit, initialize or one of the seventeen
views. Mint, burn, swap, sync and skim cannot commit (`pair_lockGuarded_unlocked`), and the
fallback reverts (`pair_bytecode_selector_inv`). Each committed frame is consumed by its
existing exact frame theorem; the finite Pair representation grows only by the frame's
actually decoded keys, which a trace-local universe `U` separates (HASH-T).
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The decoded mapping rows one Pair frame touches, by its actual selector. -/
def pairDecodedKeys (sevm : Sevm) : List WriterKey :=
  if Blanc.Sevm.selector sevm = 0xa9059cbb then
    transferTouched sevm.caller (transferRecipient sevm)
  else if Blanc.Sevm.selector sevm = 0x095ea7b3 then
    approveTouched sevm.caller (approveSpender sevm)
  else if Blanc.Sevm.selector sevm = 0x23b872dd then
    transferFromTouched (transferFromOwner sevm) sevm.caller (transferFromRecipient sevm)
  else if Blanc.Sevm.selector sevm = 0xd505accf then
    permitTouched (permitOwner sevm) (permitSpender sevm)
  else staticViewDecodedKeys sevm

/-- The locked finite representation inside a separated universe `U` of tracked rows. -/
def LockedRep (U : WriterKey → Prop) (st : State) (s : Stor) : Prop :=
  ∃ K : WriterKey → Prop, (∀ k, K k → U k) ∧ WriterRep K s st ∧ st.unlocked = 0

/-- Trace-local admission of one Pair frame's derivation: the decoded rows of every raw
Pair frame it enters (itself included, and the static Pair views its nested calls run) lie
in the universe. -/
def LockedGood (U : WriterKey → Prop) (D : Exec.Deriv) : Prop :=
  ∀ F ∈ Exec.rawFrameRoots D.exc, F.sevm.currentTarget = D.sevm.currentTarget →
    ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm, U k

/-- Raw images of the events the lock-free writers emit. -/
def lockedOwnedRaw (pair : Adr) : Event → Option Log
  | .transfer source recipient value => some (transferRawLog pair source recipient value)
  | .approval owner spender value => some (approvalRawLog pair owner spender value)
  | _ => none

/-- The source entry and nested transcript are the ones the actual selector of the frame's
derivation `D` decodes. The permit's recovery observation and turns are authenticated
against `D` itself (`PermitRecoveryAuth`): its reply, frame-entry bit and static views come
from the actual recovery STATICCALL of `D`'s own run. -/
def LockedAuth (D : Exec.Deriv) (entry : Entry) (nested : Transcript) : Prop :=
  (Blanc.Sevm.selector D.sevm = 0xa9059cbb ∧ entry = transferDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0x095ea7b3 ∧ entry = approveDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0x23b872dd ∧ entry = transferFromDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0x485cc955 ∧ entry = initializeDecodedEntry D.sevm ∧
    nested = .done) ∨
  (Blanc.Sevm.selector D.sevm = 0xd505accf ∧ entry = permitDecodedEntry D.sevm ∧
    ∃ (out : Bytes) (entered : Bool) (views : List StaticViewTurn),
      nested = .next (permitExternalResult out entered) (staticViewTranscript views .done) .done ∧
      PermitRecoveryAuth D out entered views) ∨
  (∃ view : StaticView, Blanc.Sevm.selector D.sevm = view.selector ∧
    entry = view.entry D.sevm ∧ nested = .done)

theorem LockedRep.congr {U : WriterKey → Prop} {st : State} {s s' : Stor}
    (same : ∀ k, s'.get k = s.get k) (rep : LockedRep U st s) : LockedRep U st s' := by
  obtain ⟨K, sub, wrep, locked⟩ := rep
  refine ⟨K, sub, ⟨wrep.finite, ?_, ?_, wrep.inj, wrep.apart, ?_, wrep.logicalZero⟩, locked⟩
  · have fixed := wrep.fixed
    simp only [WriterFixedMatches, same] at fixed ⊢
    exact fixed
  · intro x nonzero
    rw [same] at nonzero
    exact wrep.support x nonzero
  · intro k tracked
    rw [same]
    exact wrep.selected k tracked

private theorem locked_extend {U K : WriterKey → Prop} {keys : List WriterKey}
    (sub : ∀ k, K k → U k) (good : ∀ k ∈ keys, U k) :
    ∀ k, WriterExtend K keys k → U k := by
  intro k tracked
  rcases tracked with old | touched
  · exact sub k old
  · exact good k touched

section Outcomes

variable {U : WriterKey → Prop} (inj : WriterInj U) (apart : WriterApart U)
  {current : Checkpoint} {invocation : List Nat} {sevm : Sevm} {b post : Devm} {G : Nat}
  {K : WriterKey → Prop}
  (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
  (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
  (representable : sevm.data.length < 2 ^ 256) (sub : ∀ k, K k → U k)
  (wrep : WriterRep K (b.getStor sevm.currentTarget) current.state)
  (locked : current.state.unlocked = 0)
include inj apart run codeEq fork representable sub wrep locked

private theorem locked_transfer_outcome (selector : Blanc.Sevm.selector sevm = 0xa9059cbb)
    (good : ∀ k ∈ transferTouched sevm.caller (transferRecipient sevm), U k) :
    PairFrameOutcome sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, result, consumed⟩ := transfer_bytecode_exact_consumes
    (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine ⟨_, _, _, _, _, Or.inl ⟨selector, rfl, rfl⟩, consumed, ?_, result.sourceLogs,
    result.logs, rfl⟩
  refine ⟨_, locked_extend sub good, ?_, ?_⟩
  · rw [result.sourceState]
    exact result.representation
  · rw [result.sourceState]
    exact locked

private theorem locked_approve_outcome (selector : Blanc.Sevm.selector sevm = 0x095ea7b3)
    (good : ∀ k ∈ approveTouched sevm.caller (approveSpender sevm), U k) :
    PairFrameOutcome sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, ⟨_, representation, _, _, _, _, sourceLogs, _, _, rawLogs, _⟩,
      consumed⟩ := approve_bytecode_exact_consumes (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine ⟨_, _, _, _, _, Or.inr (Or.inl ⟨selector, rfl, rfl⟩), consumed, ?_, sourceLogs,
    rawLogs, rfl⟩
  exact ⟨_, locked_extend sub good, representation, locked⟩

private theorem locked_transferFrom_outcome (selector : Blanc.Sevm.selector sevm = 0x23b872dd)
    (good : ∀ k ∈ transferFromTouched (transferFromOwner sevm) sevm.caller
      (transferFromRecipient sevm), U k) :
    PairFrameOutcome sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, result, consumed⟩ := transferFrom_bytecode_exact_consumes
    (invocation := invocation) wrep
    (Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good) representable codeEq fork
    selector run
  refine ⟨_, _, _, _, _, Or.inr (Or.inr (Or.inl ⟨selector, rfl, rfl⟩)), consumed, ?_,
    result.sourceLogs, result.logs, rfl⟩
  refine ⟨_, locked_extend sub good, ?_, ?_⟩
  · rw [result.sourceState]
    exact result.representation
  · rw [result.sourceState]
    unfold transferFromSourceState transferFromAllowanceState
    split
    · exact locked
    · exact locked

omit inj apart in
private theorem locked_initialize_outcome (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0x485cc955) :
    PairFrameOutcome sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  obtain ⟨_, _, _, _, _, result, consumed⟩ := initialize_bytecode_exact_consumes
    (invocation := invocation) wrep representable freshOutput codeEq fork selector run
  refine ⟨_, _, _, [], [], Or.inr (Or.inr (Or.inr (Or.inl ⟨selector, rfl, rfl⟩))), consumed,
    ?_, ?_, ?_, rfl⟩
  · refine ⟨K, sub, ?_, ?_⟩
    · rw [result.sourceCurrent]
      exact result.representation
    · rw [result.sourceCurrent]
      exact locked
  · rw [result.sourceCurrent, List.append_nil]
  · rw [result.logs, List.append_nil]

private theorem locked_permit_outcome (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : b.getCode sevm.currentTarget = code) (freshOutput : b.output = [])
    (selector : Blanc.Sevm.selector sevm = 0xd505accf)
    (good : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm, U k) :
    PairFrameOutcome sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  have touched : ∀ k ∈ permitTouched (permitOwner sevm) (permitSpender sevm), U k := by
    intro k member
    apply good _ (Exec.mem_rawFrameRoots_self run) rfl k
    apply List.mem_append_left
    rw [pairDecodedKeys, ite_eq_right (by rw [selector]; decide),
      ite_eq_right (by rw [selector]; decide), ite_eq_right (by rw [selector]; decide),
      ite_eq_left selector]
    exact member
  obtain ⟨_, _, _, _, _, out, _, entered, views, auth, result, consumed, _⟩ :=
    permit_bytecode_exact_turns (invocation := invocation) inj apart sub sem image wrep touched
      (by rw [installed]; exact image.symm) representable codeEq fork selector freshOutput run
      (fun F member target k viewKey => good F member target k (List.mem_append_right _ viewKey))
  obtain ⟨_, representation, _, _, _, _, _, _, sourceLogs, _, _, rawLogs, _⟩ := result
  refine ⟨_, _, _, _, _, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨selector, rfl, out, entered, views, rfl, auth⟩)))), consumed, ?_, sourceLogs, rawLogs, rfl⟩
  exact ⟨_, locked_extend sub touched, representation, locked⟩

private theorem locked_view_outcome (view : StaticView)
    (selector : Blanc.Sevm.selector sevm = view.selector)
    (good : ∀ k ∈ staticViewDecodedKeys sevm, U k) :
    PairFrameOutcome sevm.currentTarget (LockedRep U) LockedAuth
      (lockedOwnedRaw sevm.currentTarget) current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ sevm b post := by
  have fresh := Blanc.SlotFootprint.FreshKeys.of_universe inj apart sub good
  obtain ⟨_, _, _, storage, logs, _, _, consumed, frameCurrent, _, _⟩ :=
    staticView_source_handler_selected (ctx := writerContext sevm invocation) wrep fresh
      representable rfl codeEq fork view selector run
  refine ⟨_, _, _, [], [], Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    ⟨view, selector, rfl, rfl⟩)))), consumed, ?_, ?_, ?_, rfl⟩
  · refine ⟨_, locked_extend sub good, ?_, ?_⟩
    · rw [frameCurrent, storage sevm.currentTarget]
      exact wrep.extend fresh
    · rw [frameCurrent]
      exact locked
  · rw [frameCurrent, List.append_nil]
  · rw [logs, List.append_nil]

end Outcomes

private theorem pair_view_keys {sevm : Sevm} (transfer : Blanc.Sevm.selector sevm ≠ 0xa9059cbb)
    (approve : Blanc.Sevm.selector sevm ≠ 0x095ea7b3)
    (transferFrom : Blanc.Sevm.selector sevm ≠ 0x23b872dd)
    (permit : Blanc.Sevm.selector sevm ≠ 0xd505accf) :
    pairDecodedKeys sevm = staticViewDecodedKeys sevm := by
  rw [pairDecodedKeys, ite_eq_right transfer, ite_eq_right approve, ite_eq_right transferFrom,
    ite_eq_right permit]

/-- While the Pair is locked, every committed root frame of the Pair is one exact invocation
of a lock-free entry at the current checkpoint, extending the finite representation only
by its actually decoded rows inside the separated universe `U`. -/
theorem lockedPairSupply {U : WriterKey → Prop} (inj : WriterInj U) (apart : WriterApart U)
    (sem : CodeSem) (image : sem.image = some code.toList) (pair : Adr) :
    PairFrameSupply pair (LockedRep U) (LockedGood U) LockedAuth (lockedOwnedRaw pair) := by
  intro current invocation sevm b post G run target codeEq installedCode fork freshOutput
    representable roots rep
  subst target
  have roots : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ pairDecodedKeys F.sevm ++ staticViewDecodedKeys F.sevm, U k := roots
  have good : ∀ k ∈ pairDecodedKeys sevm, U k := fun k member =>
    roots _ (Exec.mem_rawFrameRoots_self run) rfl k (List.mem_append_left _ member)
  obtain ⟨K, sub, wrep, locked⟩ := rep
  have lockedRaw : b.getStorVal sevm.currentTarget 12 = 0 :=
    wrep.fixed.2.2.2.2.2.2.2.2.2.2.2.trans locked
  have member := pair_bytecode_selector_inv codeEq fork run
  simp only [pairSelectors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.address .token1)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_permit_outcome inj apart run codeEq fork representable sub wrep locked sem image
      installedCode freshOutput h roots
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.allowance) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact absurd ((pair_lockGuarded_unlocked codeEq fork (Or.inr (Or.inr (Or.inr (Or.inl h)))) run).symm.trans
      lockedRaw) (by decide)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.constant .minimumLiquidity)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact absurd ((pair_lockGuarded_unlocked codeEq fork (Or.inr (Or.inr (Or.inr (Or.inr h)))) run).symm.trans
      lockedRaw) (by decide)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.address .factory)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.singleMapping .nonces) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact absurd ((pair_lockGuarded_unlocked codeEq fork (Or.inr (Or.inl h)) run).symm.trans
      lockedRaw) (by decide)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.string .symbol) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_transfer_outcome inj apart run codeEq fork representable sub wrep locked h
      (by rw [pairDecodedKeys, ite_eq_left h] at good; exact good)
  · exact absurd ((pair_lockGuarded_unlocked codeEq fork (Or.inl h) run).symm.trans
      lockedRaw) (by decide)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.singleMapping .balanceOf) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.stored .kLast)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.stored .domainSeparator)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_initialize_outcome run codeEq fork representable sub wrep locked freshOutput h
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.stored .price0CumulativeLast)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.stored .price1CumulativeLast)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_transferFrom_outcome inj apart run codeEq fork representable sub wrep locked h
      (by rw [pairDecodedKeys, ite_eq_right (by rw [h]; decide), ite_eq_right (by rw [h]; decide), ite_eq_left h] at good
          exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.constant .permitTypehash)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.constant .decimals)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_approve_outcome inj apart run codeEq fork representable sub wrep locked h
      (by rw [pairDecodedKeys, ite_eq_right (by rw [h]; decide), ite_eq_left h] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.scalar (.address .token0)) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.totalSupply) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact absurd ((pair_lockGuarded_unlocked codeEq fork (Or.inr (Or.inr (Or.inl h))) run).symm.trans
      lockedRaw) (by decide)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.string .name) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)
  · exact locked_view_outcome inj apart run codeEq fork representable sub wrep locked (.getReserves) (h.trans (by decide))
      (by rw [pair_view_keys (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide) (by rw [h]; decide)] at good; exact good)

end Blanc.Lift.UniswapV2Pair
