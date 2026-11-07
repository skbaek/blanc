import Blanc.Lift.BuilderRequest.Message
import Blanc.Lift.ExecCut
import Blanc.Reverts

/-!
# The builder contracts' reverting paths under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

Both runtimes have one `REVERT` site, and every path to it comes before their first `SSTORE`. These walks reuse the
exact fee path on cut trees (`Blanc/Lift/ExecCut.lean`), up to the `REVERT`, so a frame that reverts is a positive
statement: it executes `REVERT`, with its machine. `FrameReverts` is that statement, and `Submissions.message_reverts`
takes it through `processMessageCall`: pre-call state, value returned, no log, state gas restored.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestFee (PushWord selected loopTree postloopTree)
open RequestSystem (dispatchTree dispatchGas dispatch_exact dispatchArm)

/-- `JUMPDEST; PUSH0; PUSH0;` cut at the `REVERT`. -/
def rev0 : SFunc :=
  .dest (.next (.push [] (by decide)) (.next (.push [] (by decide)) (.last .stop)))

/-- The reverting arm, walked up to its `REVERT`. -/
theorem rev0_exact {fs : List SFunc} {s : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}
    (hp0 : s.benvStat.rules.op.push0 = true) (hS : S.length + 1 < 1024) :
    SFunc.RunExact fs s (St b S M (G + 2 + 2 + 1)) rev0 (.halted (St b (0 :: 0 :: S) M G)) := by
  refine rx_dest ?_
  refine rx_push0 (h_push0 := hp0) (by omega) ?_
  refine rx_push0 (h_push0 := hp0) (by show S.length + 1 < 1024; omega) ?_
  exact .last rfl

/-- `REVERT` of an empty window. -/
theorem exec_revert_empty {s : Sevm} {b : Devm} {S : List B256} {M : Mem} {G pc : Nat}
    (hat : Linst.At s.code pc .revert) :
    Nonempty (Exec pc s (St b (0 :: 0 :: S) M G) (.error (.revert, (St b S M G).withOutput []))) := by
  refine ⟨Exec.halt ?_⟩
  rw [Evm.step_last hat]
  have hz : (St b (0 :: 0 :: S) M G).extCost [((0 : B256).toNat, (0 : B256).toNat)] = 0 :=
    Devm.extCost_empty_window
  exact congrArg Step.halt (Linst.run_revert_eq_error (i := 0) (sz := 0) (s := S) rfl
    (by rw [hz]; exact Nat.zero_le _)
    (by rw [hz]; rfl))

/-- A frame from `b` on empty memory executes `REVERT` having taken a charge `X` of at most `bound` regular gas, with no
state gas. Its machine has the rest of the gas and `b`'s state-gas meter, and returns nothing. -/
def FrameReverts (s : Sevm) (b : Devm) (bound : Nat) : Prop :=
  ∃ X, X ≤ bound ∧ ∀ G, ∃ raw : Devm,
    Nonempty (Exec 0 s (St b [] .empty (G + X)) (.error (.revert, raw))) ∧
      raw.gasLeft = G ∧ raw.stateGas = b.stateGas ∧ raw.output = []

/-- A reverting path's bound: dispatch, the fee path with `n` iterations of its loop and its two `SLOAD`s, and the guards
before the `REVERT`. Regular gas; no state gas is involved. -/
def revertBound (n : Nat) : Nat := 279 + 87 * n + 2 * gasColdSload

/-- The bytes a cut program is checked against: every entry and the program in lock step. -/
def cutAll (code : ByteArray) (es : List Nat) (e : Nat) : List SFunc → List Nat → Bool
  | [], _ => true
  | f :: fs, pc :: pcs => cutOk code es e pc none f && cutAll code es e fs pcs
  | _ :: _, [] => false

theorem cutAll_spec {code : ByteArray} {es : List Nat} {e : Nat} :
    ∀ {fs : List SFunc} {pcs : List Nat}, cutAll code es e fs pcs = true →
      ∀ (k : Nat) (f : SFunc), fs[k]? = some f → ∃ pc, pcs[k]? = some pc ∧ cutOk code es e pc none f = true
  | [], _, _, _, _, h => by simp only [List.getElem?_nil, reduceCtorEq] at h
  | f0 :: fs, [], h, _, _, _ => by simp only [cutAll, Bool.false_eq_true] at h
  | f0 :: fs, pc :: pcs, h, k, f, hk => by
    simp only [cutAll, Bool.and_eq_true] at h
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      exact ⟨pc, rfl, h.1⟩
    | succ k =>
      simp only [List.getElem?_cons_succ] at hk ⊢
      exact cutAll_spec h.2 k f hk

namespace UserPath

variable (k : UserPath)

/-- The fee path's cut program: the window at entry 1 and the loop at entry 6, both builder certificates' numbering. -/
def cutProg (g t : SFunc) : List SFunc :=
  [.undefined, windowOf k.shape g t, .undefined, .undefined, .undefined, .undefined,
    loopTree k.shape.post k.shape.loop k.shape.loopEntry (postloopTree k.shape.len k.shape.submit g t)]

/-- The root of a cut fee path. -/
def cutRoot (g t : SFunc) : SFunc :=
  dispatchTree k.systemDest (feePathTree k.shape .undefined g t) .undefined

/-- A cut of the fee path checks against the bytes, with the `REVERT` at `e` and the entries at `es`. -/
structure Cut (g t : SFunc) (es : List Nat) (e : Nat) : Prop where
  all : cutAll k.code es e (k.cutProg g t) es = true
  root : cutOk k.code es e 0 none (k.cutRoot g t) = true

variable {k} {s : Sevm} {b : Devm} {M : Mem} {G : Nat} {g t : SFunc} {es : List Nat} {e : Nat}

/-- What a cut of the fee path gives: an arm walked up to the `REVERT` is a reverting execution from the frame's start,
through the fee path. -/
theorem exec_revert_of_cut (hw : k.shape.window = 1) (hl : k.shape.loopEntry = 6)
    (cut : k.Cut g t es e) (rev : Linst.At k.code e .revert) (hcode : s.code = k.code)
    (hfork : s.benvStat.fork = .amsterdam) (caller : s.caller ≠ systemAddress) {n : Nat} {out : B256}
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target s b) 17 1 17 0 n out)
    {d : Devm} {S : List B256} {M' : Mem} {G' : Nat}
    (tail : SFunc.RunExact (k.cutProg g t) s
      (St ((amsterdamSteps s).feeBase b) [out / (17 : B256)] M G)
      (selected s k.shape.len.word g t) (.halted (St d (0 :: 0 :: S) M' G'))) :
    Nonempty (Exec 0 s (St b [] M (G + (amsterdamSteps s).feePathGas b n + dispatchGas))
      (.error (.revert, (St d S M' G').withOutput []))) := by
  have path := feePath_exact (fs := k.cutProg g t) k.shape (amsterdamSteps_valid hfork) (revert := .undefined)
    (getter := g) (submission := t)
    ((congrArg (fun i => (k.cutProg g t)[i]?) hw).trans rfl)
    ((congrArg (fun i => (k.cutProg g t)[i]?) hl).trans rfl) off wordRun tail
  have root : SFunc.RunExact (k.cutProg g t) s (St b [] M (G + (amsterdamSteps s).feePathGas b n + dispatchGas))
      (k.cutRoot g t) (.halted (St d (0 :: 0 :: S) M' G')) :=
    dispatch_exact (by simpa only [dispatchArm, ite_eq_right caller] using path)
  have hat : Linst.At s.code e .revert := by rw [hcode]; exact rev
  exact exec_of_cut (es := es) (e := e) (by rw [hcode]; exact cutAll_spec cut.all) root rfl 0 none
    (by rw [hcode]; exact cut.root) (fun _ h => by cases h) (exec_revert_empty hat)

/-- The charge of a cut fee path, within `revertBound`. -/
theorem feePath_charge_le (s : Sevm) (b : Devm) (n X : Nat) (hX : X ≤ 100) :
    X + (amsterdamSteps s).feePathGas b n + dispatchGas ≤ revertBound n := by
  have a1 := sloadCost_le s b 0
  have a2 := sloadCost_le s ((amsterdamSteps s).afterRead b 0) 1
  unfold StorageSteps.feePathGas revertBound
  rw [RequestFee.feeLoopGas_eq, feePathFixedGas, dispatchGas]
  omega

/-- The two meters a read leaves alone. -/
theorem feeBase_stateGas (s : Sevm) (b : Devm) : ((amsterdamSteps s).feeBase b).stateGas = b.stateGas := by
  show (afterSloadA s (afterSloadA s b 0) 1).stateGas = _
  rw [afterSloadA_stateGas, afterSloadA_stateGas]

/-- **Reverting through the fee path.** A contract's arm walked up to the `REVERT`, at a cost `X` of at most 100 regular
gas, gives `FrameReverts`. -/
theorem frameReverts_of_arm (hw : k.shape.window = 1) (hl : k.shape.loopEntry = 6)
    (cut : k.Cut g t es e) (rev : Linst.At k.code e .revert) (hcode : s.code = k.code)
    (hfork : s.benvStat.fork = .amsterdam) (caller : s.caller ≠ systemAddress) {n : Nat} {out : B256}
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target s b) 17 1 17 0 n out)
    {S : List B256} {X : Nat} (hX : X ≤ 100)
    (tail : ∀ G, SFunc.RunExact (k.cutProg g t) s
      (St ((amsterdamSteps s).feeBase b) [out / (17 : B256)] .empty (G + X))
      (selected s k.shape.len.word g t)
      (.halted (St ((amsterdamSteps s).feeBase b) (0 :: 0 :: S) .empty G))) :
    FrameReverts s b (revertBound n) := by
  refine ⟨X + (amsterdamSteps s).feePathGas b n + dispatchGas, feePath_charge_le s b n X hX, fun G => ?_⟩
  refine ⟨(St ((amsterdamSteps s).feeBase b) S .empty G).withOutput [], ?_, rfl, feeBase_stateGas s b, rfl⟩
  have hrun := exec_revert_of_cut hw hl cut rev hcode hfork caller off wordRun (tail G)
  have hgas : G + (X + (amsterdamSteps s).feePathGas b n + dispatchGas) =
      G + X + (amsterdamSteps s).feePathGas b n + dispatchGas := by
    simp only [Nat.add_assoc]
  rw [hgas]
  exact hrun

/-- The getter arm cut for wrong calldata: `CALLDATASIZE` nonzero takes the `REVERT`. -/
def badLengthCut (k : UserPath) : SFunc :=
  (.next (.reg .calldatasize) (.next (.push (k.getterDest.head :: k.getterDest.tail) k.getterDest.le)
    (.branch .undefined rev0)))

/-- The getter arm cut for a fee read carrying value: `CALLVALUE` nonzero takes the `REVERT`. -/
def paidReadCut (k : UserPath) : SFunc :=
  (.next (.reg .calldatasize) (.next (.push (k.getterDest.head :: k.getterDest.tail) k.getterDest.le)
    (.branch (.next (.reg .callvalue) (.next (.push (k.getterDest.head :: k.getterDest.tail) k.getterDest.le)
      (.branch .undefined rev0))) .undefined)))

/-- **Calldata of neither form.** At a length that is neither the submission's nor zero, the frame executes `REVERT`. -/
theorem frameReverts_badLength (hw : k.shape.window = 1) (hl : k.shape.loopEntry = 6)
    (cut : k.Cut (badLengthCut k) .undefined es e) (rev : Linst.At k.code e .revert) (hcode : s.code = k.code)
    (hfork : s.benvStat.fork = .amsterdam) (caller : s.caller ≠ systemAddress) {n : Nat} {out : B256}
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target s b) 17 1 17 0 n out)
    (other : s.data.length.toB256 ≠ k.shape.len.word) (nonzero : s.data.length.toB256 ≠ 0) :
    FrameReverts s b (revertBound n) := by
  refine frameReverts_of_arm (X := 5 + 10 + 3 + 2) (S := [out / (17 : B256)]) hw hl cut rev hcode hfork caller off
    wordRun (by omega) fun G => ?_
  simp only [selected, ite_eq_right other]
  have hgas : G + (5 + 10 + 3 + 2) = (G + 2 + 2 + 1) + 10 + 3 + 2 := by omega
  rw [hgas]
  unfold badLengthCut
  refine rx_calldatasize (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  exact rx_branch_succ nonzero (rev0_exact (amsterdam_push0 hfork) (by change 2 < 1024; decide))

/-- **A fee read carrying value.** Empty calldata and nonzero value: the frame executes `REVERT`. -/
theorem frameReverts_paidRead (hw : k.shape.window = 1) (hl : k.shape.loopEntry = 6)
    (cut : k.Cut (paidReadCut k) .undefined es e) (rev : Linst.At k.code e .revert) (hcode : s.code = k.code)
    (hfork : s.benvStat.fork = .amsterdam) (caller : s.caller ≠ systemAddress) {n : Nat} {out : B256}
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target s b) 17 1 17 0 n out)
    (empty : s.data = []) (paid : s.value ≠ 0) :
    FrameReverts s b (revertBound n) := by
  have other : s.data.length.toB256 ≠ k.shape.len.word := by
    rw [empty]
    exact k.len_ne.symm
  have zero : s.data.length.toB256 = 0 := by rw [empty]; rfl
  refine frameReverts_of_arm (X := 5 + 10 + 3 + 2 + 10 + 3 + 2) (S := [out / (17 : B256)]) hw hl cut rev hcode hfork
    caller off wordRun (by omega) fun G => ?_
  simp only [selected, ite_eq_right other]
  have hgas : G + (5 + 10 + 3 + 2 + 10 + 3 + 2) = (G + 2 + 2 + 1) + 10 + 3 + 2 + 10 + 3 + 2 := by omega
  rw [hgas]
  unfold paidReadCut
  refine rx_calldatasize (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  rw [zero]
  refine rx_branch_zero ?_
  refine rx_callvalue (by change 1 < 1024; decide) ?_
  refine rx_push rfl (by change 2 < 1024; decide) ?_
  exact rx_branch_succ paid (rev0_exact (amsterdam_push0 hfork) (by change 2 < 1024; decide))

end UserPath

/-- The inhibitor path's cut tree: slot 0 on the inhibitor takes the `REVERT`. -/
def inhibitCut (systemDest revert : PushWord) : SFunc :=
  dispatchTree systemDest (inhibitorTree revert .undefined rev0) .undefined

/-- **While slot 0 holds the inhibitor, a non-system frame executes `REVERT`.** Any calldata, value and storage. -/
theorem frameReverts_inhibited {code : ByteArray} {systemDest revert : PushWord} {e : Nat} {s : Sevm} {b : Devm}
    (root : cutOk code [] e 0 none (inhibitCut systemDest revert) = true) (rev : Linst.At code e .revert)
    (hcode : s.code = code) (hfork : s.benvStat.fork = .amsterdam) (caller : s.caller ≠ systemAddress)
    (inhibited : b.getStorVal s.currentTarget 0 = B256.max) :
    FrameReverts s b (revertBound 0) := by
  have hp0 := amsterdam_push0 hfork
  have a0 := sloadCost_le s b 0
  refine ⟨5 + 10 + 3 + 3 + 3 + 3 + sloadCost s b 0 + 2 + dispatchGas, ?_, fun G => ?_⟩
  · unfold revertBound
    rw [dispatchGas]
    omega
  refine ⟨(St (afterSloadA s b 0) [B256.max] .empty G).withOutput [], ?_, rfl, afterSloadA_stateGas, rfl⟩
  have run : SFunc.RunExact [] s
      (St b [] .empty (G + (5 + 10 + 3 + 3 + 3 + 3 + sloadCost s b 0 + 2 + dispatchGas)))
      (inhibitCut systemDest revert) (.halted (St (afterSloadA s b 0) [0, 0, B256.max] .empty G)) := by
    have hgas : G + (5 + 10 + 3 + 3 + 3 + 3 + sloadCost s b 0 + 2 + dispatchGas) =
        (G + 2 + 2 + 1) + 10 + 3 + 3 + 3 + 3 + sloadCost s b 0 + 2 + dispatchGas := by
      omega
    rw [hgas]
    refine dispatch_exact ?_
    simp only [dispatchArm, ite_eq_right caller]
    unfold inhibitorTree
    refine rx_push0 (h_push0 := hp0) (by change 0 < 1024; decide) ?_
    refine rx_sloadV (amsterdam_access hfork) (by change 0 < 1024; decide) inhibited ?_
    refine rx_dup1 (by change 1 < 1024; decide) ?_
    refine rx_push inhibitor_push (by change 2 < 1024; decide) ?_
    refine rx_eq (v := 1) (by decide) (by change 1 < 1024; decide) ?_
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    exact rx_branch_succ (by decide : (1 : B256) ≠ 0) (rev0_exact hp0 (by change 2 < 1024; decide))
  have hat : Linst.At s.code e .revert := by rw [hcode]; exact rev
  exact exec_of_cut (fs := []) (es := []) (e := e) (fun _ _ h => by simp only [List.getElem?_nil, reduceCtorEq] at h) run
    rfl 0 none (by rw [hcode]; exact root) (fun _ h => by cases h) (exec_revert_empty hat)

namespace Submissions

variable (c : Submissions) {M : Msg} {benv : Benv}

/-- The frame's static environment at a message to the code. -/
local notation "S" => userSevm M c.code benv

/-- The frame's entry machine. -/
local notation "E" => userEntry M benv

/-- **A direct message whose frame reverts, under Amsterdam.** The call returns the state before it, so the value is
back. No log survives, the EIP-7708 transfer log included. The regular gas left is the message's less the frame's charge
`X`, at most `bound` (regular gas; the frame charges no state gas before its `REVERT`). The reservoir is at its grant, no
state gas is used, and the call returns nothing. -/
theorem message_reverts {bound : Nat} (hfork : M.benv.stat.fork = .amsterdam)
    (hauth : M.tenv.stat.auths.isEmpty = true) (htarget : M.target.isNone = false)
    (installed : M.benv.state.getCode M.currentTarget = c.code)
    (hprecomp : ¬ amsterdamRules.isPrecomp M.currentTarget) (entry : M.benvAfterTransfer = .ok benv)
    (hrev : FrameReverts S E bound) (hgas : bound ≤ M.gas) :
    ∃ X, X ≤ bound ∧ ∃ out : MsgCallOutput, processMessageCall M = .ok (M.benv.state, out) ∧
      out.logs = [] ∧ out.error = some .revert ∧ out.gasLeft = M.gas - X ∧ out.stateGasLeft = M.stateGasGrant ∧
      out.stateGasUsed = 0 ∧ out.refundCounter = 0 ∧ out.returnData = [] ∧
      out.accountsToDelete.toList = [] := by
  obtain ⟨X, hX, hrun⟩ := hrev
  obtain ⟨raw, ⟨hexec⟩, hleft, hmeter, houtput⟩ := hrun (M.gas - X)
  have hSt : St (E) [] .empty (M.gas - X + X) = E := by
    rw [show M.gas - X + X = M.gas by omega]
    exact (St.self rfl rfl).symm
  rw [hSt] at hexec
  have hcall := processMessageCall_revert hfork hauth htarget installed c.nonempty c.undelegated hprecomp entry
    ((exec_iff_exec_eq _ _ _ _).mp ⟨hexec⟩)
  obtain ⟨m1, m2, m3, m4, m5, m6⟩ := failedOutput_revert M raw
  have hspill : raw.stateGas.spilled = 0 := by rw [hmeter]; rfl
  have hbase : raw.stateGas.baseline = M.stateGasGrant := by rw [hmeter]; rfl
  have hcommit : raw.stateGas.committedSpill = 0 := by rw [hmeter]; rfl
  refine ⟨X, hX, _, hcall, m4, m5, ?_, ?_, ?_, m3, houtput, Std.HashSet.toList_emptyWithCapacity⟩
  · rw [m2, hleft, hspill]
    rfl
  · rw [m1, hbase]
  · rw [m6, hbase, hcommit]
    simp only [Int.ofNat_eq_natCast, Int.natCast_zero, Int.add_zero, Int.sub_self]

end Submissions

end Blanc.Lift.BuilderRequest
