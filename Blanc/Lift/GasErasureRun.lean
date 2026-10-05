import Blanc.GasErasure
import Blanc.Lift.Silent
import Blanc.ForwardCall

/-!
# Gas erasure over a lifted run

Contract-neutral.  `Blanc/GasErasure.lean` replays two successful runs of one gas-free instruction
or line against each other modulo `gasLeft`.  This module extends that to whole synthetic runs:

* `Ninst.gasFreeRun` widens the instruction whitelist by `KECCAK256` and `LOG n` (their successful
  effects read memory and pay for it, but never read `gasLeft`), with `Ninst.run_eqModGasRun`;
* `Linst.run_eqModGas`: two successful runs of `STOP` or `RETURN` agree modulo gas;
* `SFunc.gasFree` / `GasFreeSet`: a kernel-checkable certificate that a tree and every entry it can
  reach contain only such instructions (no `PC`, no external instruction, no `SELFDESTRUCT`);
* `SFunc.RunP.eqModGas`: two successful runs of a certified tree from states equal modulo gas end
  the same way (both halt or both return) in states equal modulo gas.

The consumer pattern: an arbitrary successful frame and a constructed gas-exact run of the same code
from the same state with more gas have the same output, storage, logs and every other column but
`gasLeft`, so a forward walk's output facts transfer to the actual frame without a gas premise.
-/

namespace Blanc

open Jaune

/-! ## Agreement under the remaining updates -/

theorem Devm.EqModGas.withGasLeft (a : Devm) (g : Nat) : EqModGas a (a.withGasLeft g) :=
  ⟨rfl, rfl, trivial, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Devm.EqModGas.of_withOutput {a b : Devm} (o : Bytes) (h : EqModGas a b) :
    EqModGas (a.withOutput o) (b.withOutput o) :=
  ⟨h.stack, h.memory, trivial, h.logs, h.refundCounter, rfl, h.accountsToDelete, h.returnData,
    h.error, h.accessedAddresses, h.accessedStorageKeys, h.state, h.createdAccounts,
    h.transientStorage, h.stateGas, h.accountReads, h.storageReads⟩

theorem Devm.EqModGas.of_addLog {a b : Devm} (l : Log) (h : EqModGas a b) :
    EqModGas (a.addLog l) (b.addLog l) :=
  ⟨h.stack, h.memory, trivial, congrArg (· ++ [l]) h.logs, h.refundCounter, h.output,
    h.accountsToDelete, h.returnData, h.error, h.accessedAddresses, h.accessedStorageKeys, h.state,
    h.createdAccounts, h.transientStorage, h.stateGas, h.accountReads, h.storageReads⟩

theorem Devm.EqModGas.output_eq {a b : Devm} (h : EqModGas a b) : a.output = b.output := h.output

/-- Two pops of equally many words from agreeing states pop the same words onto agreeing states. -/
theorem Devm.EqModGas.of_popList {a a₁ b b₁ : Devm} {xs ys : List B256}
    (h1 : Devm.Pop xs a a₁) (h2 : Devm.Pop ys b b₁) (hlen : xs.length = ys.length)
    (h : EqModGas a b) : xs = ys ∧ EqModGas a₁ b₁ := by
  have hst : xs ++ a₁.stack = ys ++ b₁.stack := h1.stack.symm.trans (h.stack.trans h2.stack)
  obtain ⟨hxy, hstk⟩ := List.append_inj hst hlen
  exact ⟨hxy, ⟨hstk, h1.memory.symm.trans (h.memory.trans h2.memory), trivial,
    h1.logs.symm.trans (h.logs.trans h2.logs),
    h1.refundCounter.symm.trans (h.refundCounter.trans h2.refundCounter),
    h1.output.symm.trans (h.output.trans h2.output),
    h1.accountsToDelete.symm.trans (h.accountsToDelete.trans h2.accountsToDelete),
    h1.returnData.symm.trans (h.returnData.trans h2.returnData),
    h1.error.symm.trans (h.error.trans h2.error),
    h1.accessedAddresses.symm.trans (h.accessedAddresses.trans h2.accessedAddresses),
    h1.accessedStorageKeys.symm.trans (h.accessedStorageKeys.trans h2.accessedStorageKeys),
    h1.state.symm.trans (h.state.trans h2.state),
    h1.createdAccounts.symm.trans (h.createdAccounts.trans h2.createdAccounts),
    h1.transientStorage.symm.trans (h.transientStorage.trans h2.transientStorage),
    h1.stateGas.symm.trans (h.stateGas.trans h2.stateGas),
    h1.accountReads.symm.trans (h.accountReads.trans h2.accountReads),
    h1.storageReads.symm.trans (h.storageReads.trans h2.storageReads)⟩⟩

/-- Two `PopBurn`s of equally many words from agreeing states pop the same words onto agreeing
states. -/
theorem Devm.EqModGas.of_popBurnList {a a₁ b b₁ : Devm} {xs ys : List B256}
    (h1 : Devm.PopBurn xs a a₁) (h2 : Devm.PopBurn ys b b₁) (hlen : xs.length = ys.length)
    (h : EqModGas a b) : xs = ys ∧ EqModGas a₁ b₁ := by
  have hst : xs ++ a₁.stack = ys ++ b₁.stack := h1.stack.symm.trans (h.stack.trans h2.stack)
  obtain ⟨hxy, hstk⟩ := List.append_inj hst hlen
  exact ⟨hxy, ⟨hstk, h1.memory.symm.trans (h.memory.trans h2.memory), trivial,
    h1.logs.symm.trans (h.logs.trans h2.logs),
    h1.refundCounter.symm.trans (h.refundCounter.trans h2.refundCounter),
    h1.output.symm.trans (h.output.trans h2.output),
    h1.accountsToDelete.symm.trans (h.accountsToDelete.trans h2.accountsToDelete),
    h1.returnData.symm.trans (h.returnData.trans h2.returnData),
    h1.error.symm.trans (h.error.trans h2.error),
    h1.accessedAddresses.symm.trans (h.accessedAddresses.trans h2.accessedAddresses),
    h1.accessedStorageKeys.symm.trans (h.accessedStorageKeys.trans h2.accessedStorageKeys),
    h1.state.symm.trans (h.state.trans h2.state),
    h1.createdAccounts.symm.trans (h.createdAccounts.trans h2.createdAccounts),
    h1.transientStorage.symm.trans (h.transientStorage.trans h2.transientStorage),
    h1.stateGas.symm.trans (h.stateGas.trans h2.stateGas),
    h1.accountReads.symm.trans (h.accountReads.trans h2.accountReads),
    h1.storageReads.symm.trans (h.storageReads.trans h2.storageReads)⟩⟩

/-! ## `KECCAK256` and `LOG n` -/

private theorem run_keccak {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat}
    (h1 : Rinst.run ⟨pc1, e, a⟩ .keccak256 = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ .keccak256 = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨i1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨i2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨⟨n1, a2⟩, hq1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨n2, b2⟩, hq2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨a3, hc1, hpush1⟩
  rcases Except.bind_eq_ok h2 with ⟨b3, hc2, hpush2⟩
  obtain ⟨hii, hag1⟩ := Devm.EqModGas.of_popToNat hp1 hp2 h
  obtain ⟨hnn, hag2⟩ := Devm.EqModGas.of_popToNat hq1 hq2 hag1
  subst hii hnn
  have hag3 := hag2.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  obtain ⟨hval, hagm⟩ := hag3.memRead_congr (i := i1) (n := n1)
  generalize a3.memRead i1 n1 = m1 at hpush1 hval hagm
  generalize b3.memRead i1 n1 = m2 at hpush2 hval hagm
  rcases m1 with ⟨v1, d1⟩
  rcases m2 with ⟨v2, d2⟩
  dsimp only at hpush1 hpush2 hval hagm
  rw [hval] at hpush1
  exact hagm.of_push (Devm.push_of_push hpush1) (Devm.push_of_push hpush2)

private theorem run_log {e : Sevm} {a a' b b' : Devm} {pc1 pc2 : Nat} {n : Fin 5}
    (h1 : Rinst.run ⟨pc1, e, a⟩ (.log n) = .ok a')
    (h2 : Rinst.run ⟨pc2, e, b⟩ (.log n) = .ok b')
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  simp only [Rinst.run, Rinst.runCore] at h1 h2
  rcases Except.bind_eq_ok h1 with ⟨⟨i1, a1⟩, hp1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨i2, b1⟩, hp2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨⟨n1, a2⟩, hq1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨n2, b2⟩, hq2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨⟨t1, a3⟩, ht1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨⟨t2, b3⟩, ht2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨a4, hc1, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨b4, hc2, h2⟩
  rcases Except.bind_eq_ok h1 with ⟨u1, -, h1⟩
  rcases Except.bind_eq_ok h2 with ⟨u2, -, h2⟩
  obtain ⟨hii, hag1⟩ := Devm.EqModGas.of_popToNat hp1 hp2 h
  obtain ⟨hnn, hag2⟩ := Devm.EqModGas.of_popToNat hq1 hq2 hag1
  obtain ⟨hl1, hpop1⟩ := Devm.pop_of_popN ht1
  obtain ⟨hl2, hpop2⟩ := Devm.pop_of_popN ht2
  obtain ⟨htt, hag3⟩ := hag2.of_popList hpop1 hpop2 (hl1.trans hl2.symm)
  subst hii hnn htt
  have hag4 := hag3.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
  obtain ⟨hval, hagm⟩ := hag4.memRead_congr (i := i1) (n := n1)
  generalize a4.memRead i1 n1 = m1 at h1 hval hagm
  generalize b4.memRead i1 n1 = m2 at h2 hval hagm
  rcases m1 with ⟨v1, d1⟩
  rcases m2 with ⟨v2, d2⟩
  dsimp only at h1 h2 hval hagm
  injection h1 with h1
  injection h2 with h2
  rw [← h1, ← h2, hval]
  exact hagm.of_addLog _

/-! ## The widened whitelist -/

/-- The gas-free regular instructions of `Rinst.gasFree` plus `KECCAK256` and `LOG n`. -/
def Rinst.gasFreeRun : Rinst → Bool
  | .keccak256 => true
  | .log _ => true
  | r => Rinst.gasFree r

/-- `Ninst.gasFree` over the widened regular whitelist. -/
def Ninst.gasFreeRun : Ninst → Bool
  | .reg r => Rinst.gasFreeRun r
  | .push _ _ => true
  | _ => false

theorem Ninst.run_eqModGasRun {e : Sevm} {a a' b b' : Devm} {i : Ninst}
    (hfree : Ninst.gasFreeRun i = true)
    (h1 : Ninst.Run e a i a') (h2 : Ninst.Run e b i b')
    (h : Devm.EqModGas a b)
    (hsg : e.benvStat.rules.stateGas = none) : Devm.EqModGas a' b' := by
  cases i with
  | reg r =>
    rcases of_run_reg h1 with ⟨pc1, run1⟩
    rcases of_run_reg h2 with ⟨pc2, run2⟩
    cases r with
    | keccak256 => exact run_keccak run1 run2 h
    | log n => exact run_log run1 run2 h
    | _ =>
      exact Rinst.run_eqModGas (by simpa only [Ninst.gasFreeRun, Rinst.gasFreeRun] using hfree)
        run1 run2 h hsg
  | push xs le =>
    exact h.of_pushBurn (of_run_push h1) (of_run_push h2)
  | exec x => simp only [Ninst.gasFreeRun, Bool.false_eq_true] at hfree
  | dupn u => simp only [Ninst.gasFreeRun, Bool.false_eq_true] at hfree
  | swapn u => simp only [Ninst.gasFreeRun, Bool.false_eq_true] at hfree
  | exchange u => simp only [Ninst.gasFreeRun, Bool.false_eq_true] at hfree

/-! ## Terminals -/

/-- The terminals whose successful effect never reads `gasLeft`: `STOP` and `RETURN`
(`REVERT` never succeeds). -/
def Linst.gasFree : Linst → Bool
  | .stop => true
  | .return_ => true
  | .revert => true
  | _ => false

theorem Linst.run_eqModGas {e : Sevm} {a a' b b' : Devm} {l : Linst}
    (hfree : Linst.gasFree l = true)
    (h1 : Linst.Run e a l (.ok a')) (h2 : Linst.Run e b l (.ok b'))
    (h : Devm.EqModGas a b) : Devm.EqModGas a' b' := by
  cases l with
  | stop =>
    injection h1 with h1
    injection h2 with h2
    rw [← h1, ← h2]
    exact h
  | return_ =>
    simp only [Linst.Run, Linst.run] at h1 h2
    rcases Except.bind_eq_ok h1 with ⟨⟨i1, a1⟩, hp1, h1⟩
    rcases Except.bind_eq_ok h2 with ⟨⟨i2, b1⟩, hp2, h2⟩
    rcases Except.bind_eq_ok h1 with ⟨⟨n1, a2⟩, hq1, h1⟩
    rcases Except.bind_eq_ok h2 with ⟨⟨n2, b2⟩, hq2, h2⟩
    rcases Except.bind_eq_ok h1 with ⟨a3, hc1, h1⟩
    rcases Except.bind_eq_ok h2 with ⟨b3, hc2, h2⟩
    obtain ⟨hii, hag1⟩ := Devm.EqModGas.of_popToNat hp1 hp2 h
    obtain ⟨hnn, hag2⟩ := Devm.EqModGas.of_popToNat hq1 hq2 hag1
    subst hii hnn
    have hag3 := hag2.of_burn (Devm.burn_of_chargeGas hc1) (Devm.burn_of_chargeGas hc2)
    obtain ⟨hval, hagm⟩ := hag3.memRead_congr (i := i1) (n := n1)
    generalize a3.memRead i1 n1 = m1 at h1 hval hagm
    generalize b3.memRead i1 n1 = m2 at h2 hval hagm
    rcases m1 with ⟨v1, d1⟩
    rcases m2 with ⟨v2, d2⟩
    dsimp only at h1 h2 hval hagm
    injection h1 with h1
    injection h2 with h2
    rw [← h1, ← h2, hval]
    exact hagm.of_withOutput _
  | revert =>
    simp only [Linst.Run, Linst.run] at h1
    rcases Except.bind_eq_ok h1 with ⟨⟨i1, a1⟩, -, h1⟩
    rcases Except.bind_eq_ok h1 with ⟨⟨n1, a2⟩, -, h1⟩
    rcases Except.bind_eq_ok h1 with ⟨a3, -, h1⟩
    cases h1
  | _ => simp only [Linst.gasFree, Bool.false_eq_true] at hfree

/-! ## Gas-independent forward cost helpers -/

theorem Devm.EqModGas.accessedStorageKeys_eq {a b : Devm} (h : EqModGas a b) :
    a.accessedStorageKeys = b.accessedStorageKeys := h.accessedStorageKeys

theorem Devm.EqModGas.refundCounter_eq {a b : Devm} (h : EqModGas a b) :
    a.refundCounter = b.refundCounter := h.refundCounter

theorem Devm.EqModGas.sloadCost_congr {a b : Devm} (sevm : Sevm) (k : B256) (h : EqModGas a b) :
    sloadCost sevm a k = sloadCost sevm b k := by
  unfold sloadCost
  rw [h.accessedStorageKeys_eq]

theorem Devm.EqModGas.sstoreCost_congr {a b : Devm} (sevm : Sevm) (k v : B256) (h : EqModGas a b) :
    sstoreCost sevm a k v = sstoreCost sevm b k v := by
  unfold sstoreCost
  rw [h.accessedStorageKeys_eq, h.getStorVal_congr]

theorem Devm.EqModGas.afterSload {a b : Devm} (sevm : Sevm) (k : B256) (h : EqModGas a b) :
    EqModGas (afterSload sevm a k) (afterSload sevm b k) := by
  unfold Blanc.afterSload
  rw [h.accessedStorageKeys_eq]
  split_ifs
  · exact h
  · exact h.of_addAccessedStorageKey

theorem Devm.EqModGas.afterSstore {a b : Devm} (sevm : Sevm) (k v : B256) (h : EqModGas a b) :
    EqModGas (afterSstore sevm a k v) (afterSstore sevm b k v) := by
  unfold Blanc.afterSstore
  dsimp only
  rw [h.accessedStorageKeys_eq, h.getStorVal_congr, h.refundCounter_eq]
  split_ifs
  · exact h.of_withRefundCounter.of_setStorVal
  · exact h.of_addAccessedStorageKey.of_withRefundCounter.of_setStorVal

end Blanc

namespace Blanc.Lift

open Jaune Blanc

/-! ## The tree certificate -/

/-- A synthetic tree whose instructions and terminals are all in the widened gas-free whitelist
(no `PC` node). -/
def SFunc.gasFree : SFunc → Bool
  | .branch f g => f.gasFree && g.gasFree
  | .branchTo f _ => f.gasFree
  | .last l => Linst.gasFree l
  | .next n f => Ninst.gasFreeRun n && f.gasFree
  | .dest f => f.gasFree
  | .jump _ => true
  | .callNext _ f => f.gasFree
  | .ret => true
  | .pcAt _ _ => false
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, each of which is gas-free. -/
def GasFreeSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.gasFree && g.refs.all (· ∈ S)
    | none => false

/-- Two synthetic outcomes of the same kind whose states agree modulo gas. -/
def Outcome.EqModGas : Outcome → Outcome → Prop
  | .halted a, .halted b => Devm.EqModGas a b
  | .returned a, .returned b => Devm.EqModGas a b
  | _, _ => False

/-- **Two successful runs of a gas-free tree from states equal modulo gas end the same way, in states
equal modulo gas.**  The first run may record more about its steps (`P`, e.g. the actual derivation
nodes); the second is any run (e.g. a constructed gas-exact one). -/
theorem SFunc.RunP.eqModGas {P Q : Sevm → Devm → Ninst → Devm → Prop}
    (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (hQ : ∀ {s d n d'}, Q s d n d' → Ninst.Run s d n d')
    {fs : List SFunc} {S : List Nat} (hS : GasFreeSet fs S = true) {sevm : Sevm}
    (hsg : sevm.benvStat.rules.stateGas = none) {a : Devm} {f : SFunc} {o : Outcome}
    (hf : f.gasFree = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm a f o) :
    ∀ {b : Devm} {o' : Outcome}, SFunc.RunP Q fs sevm b f o' → Devm.EqModGas a b →
      Outcome.EqModGas o o' := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.gasFree = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  induction run with
  | zero d pop _ ih =>
    intro b o' run' h
    simp only [SFunc.gasFree, Bool.and_eq_true] at hf
    simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
    cases run' with
    | zero d' pop' run' =>
      exact ih hf.1 hrefs.1 run' (h.of_popBurnList pop pop' rfl).2
    | succ d' w hw pop' run' =>
      exact absurd (List.cons.inj (List.cons.inj (h.of_popBurnList pop pop' rfl).1).2).1.symm hw
  | succ d w hw pop _ ih =>
    intro b o' run' h
    simp only [SFunc.gasFree, Bool.and_eq_true] at hf
    simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
    cases run' with
    | zero d' pop' run' =>
      exact absurd (List.cons.inj (List.cons.inj (h.of_popBurnList pop pop' rfl).1).2).1 hw
    | succ d' w' hw' pop' run' =>
      exact ih hf.2 hrefs.2 run' (h.of_popBurnList pop pop' rfl).2
  | toZero d pop _ ih =>
    intro b o' run' h
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
    cases run' with
    | toZero d' pop' run' =>
      exact ih hf hrefs.2 run' (h.of_popBurnList pop pop' rfl).2
    | toSucc d' w hw lookup' pop' run' =>
      exact absurd (List.cons.inj (List.cons.inj (h.of_popBurnList pop pop' rfl).1).2).1.symm hw
  | toSucc d w hw lookup pop _ ih =>
    intro b o' run' h
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
    have htarget := closed (of_decide_eq_true hrefs.1) lookup
    cases run' with
    | toZero d' pop' run' =>
      exact absurd (List.cons.inj (List.cons.inj (h.of_popBurnList pop pop' rfl).1).2).1 hw
    | toSucc d' w' hw' lookup' pop' run' =>
      rw [lookup] at lookup'
      cases lookup'
      exact ih htarget.1 htarget.2 run' (h.of_popBurnList pop pop' rfl).2
  | last hrun =>
    intro b o' run' h
    cases run' with
    | last hrun' => exact Linst.run_eqModGas hf hrun hrun' h
  | next hstep _ ih =>
    intro b o' run' h
    simp only [SFunc.gasFree, Bool.and_eq_true] at hf
    cases run' with
    | next hstep' run' =>
      exact ih hf.2 hrefs run' (Ninst.run_eqModGasRun hf.1 (hP hstep) (hQ hstep') h hsg)
  | dest burn _ ih =>
    intro b o' run' h
    cases run' with
    | dest burn' run' => exact ih hf hrefs run' (h.of_burn burn burn')
  | jump d lookup pop _ ih =>
    intro b o' run' h
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
    have htarget := closed (of_decide_eq_true hrefs.1) lookup
    cases run' with
    | jump d' lookup' pop' run' =>
      rw [lookup] at lookup'
      cases lookup'
      exact ih htarget.1 htarget.2 run' (h.of_popBurnList pop pop' rfl).2
  | ret d pop =>
    intro b o' run' h
    cases run' with
    | ret d' pop' => exact (h.of_popBurnList pop pop' rfl).2
  | callHalt d lookup pop _ ih =>
    intro b o' run' h
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
    have htarget := closed (of_decide_eq_true hrefs.1) lookup
    cases run' with
    | callHalt d' lookup' pop' run' =>
      rw [lookup] at lookup'
      cases lookup'
      exact ih htarget.1 htarget.2 run' (h.of_popBurnList pop pop' rfl).2
    | callRet d' lookup' pop' run' tail' =>
      rw [lookup] at lookup'
      cases lookup'
      exact False.elim (ih htarget.1 htarget.2 run' (h.of_popBurnList pop pop' rfl).2)
  | callRet d lookup pop _ _ ihRun ihTail =>
    intro b o' run' h
    simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
    have htarget := closed (of_decide_eq_true hrefs.1) lookup
    simp only [SFunc.gasFree] at hf
    cases run' with
    | callHalt d' lookup' pop' run' =>
      rw [lookup] at lookup'
      cases lookup'
      exact False.elim (ihRun htarget.1 htarget.2 run' (h.of_popBurnList pop pop' rfl).2)
    | callRet d' lookup' pop' run' tail' =>
      rw [lookup] at lookup'
      cases lookup'
      exact ihTail hf hrefs.2 tail'
        (ihRun htarget.1 htarget.2 run' (h.of_popBurnList pop pop' rfl).2)
  | pcAt _ _ _ _ =>
    simp only [SFunc.gasFree, Bool.false_eq_true] at hf

end Blanc.Lift
