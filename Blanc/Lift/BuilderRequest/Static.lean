import Blanc.Lift.BuilderRequest.Revert

/-!
# Builder frames in a static context, under Amsterdam

**Build target.** Jaune pin `e8db2742`, built on `tests@v21.0.1`, EELS `1562e2f`.

What a `STATICCALL` reaches is a frame with `isStatic` set. A fee read is unaffected (`exec_fee_read_effects` has no `isStatic` premise). A
submission gets through the fee path and its guards, reads the count, and fails at its first `SSTORE` with `writeInStaticContext`. **These are
frame-level statements**: they do not say what the calling frame does with the failure or the quote, and `processMessageCall` is not the path
a `STATICCALL` takes.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune
open RequestFee (selected)
open RequestSystem (dispatchTree dispatchGas dispatch_exact dispatchArm)

/-- `SSTORE` in a static frame, under Amsterdam, halts with `writeInStaticContext`, before any other check. -/
theorem exec_sstore_static {s : Sevm} {b : Devm} {S : List B256} {M : Mem} {G pc : Nat} {k v : B256}
    (hfork : s.benvStat.fork = .amsterdam) (hs : s.isStatic = true) (hat : Ninst.At s.code pc (.reg .sstore)) :
    ∃ raw, Nonempty (Exec pc s (St b (k :: v :: S) M G) (.error (.halt (.writeInStaticContext .none), raw))) := by
  have hsg := amsterdam_stateGas hfork
  refine ⟨St b (k :: v :: S) M G, ⟨Exec.halt ?_⟩⟩
  rw [Evm.step_next hat]
  simp only [Ninst.step, Rinst.run, Rinst.runCore, hsg, bind, Except.bind, assertDynamic, Except.assert, hs,
    Bool.not_true, Bool.false_eq_true, ↓reduceIte, Step.ofExecution]

namespace UserPath

variable {k : UserPath} {s : Sevm} {b : Devm} {M : Mem} {G : Nat} {g t : SFunc} {es : List Nat} {e : Nat}

/-- An arm walked up to a cut is a prefix, through the fee path, of whatever execution continues from the cut. -/
theorem exec_of_arm (hw : k.shape.window = 1) (hl : k.shape.loopEntry = 6)
    (cut : k.Cut g t es e) (hcode : s.code = k.code)
    (hfork : s.benvStat.fork = .amsterdam) (caller : s.caller ≠ systemAddress) {n : Nat} {out : B256}
    (off : b.getStorVal s.currentTarget 0 ≠ B256.max)
    (wordRun : WordFakeExponential.Run (storedExcess k.target s b) 17 1 17 0 n out)
    {d : Devm} {ex : Execution}
    (tail : SFunc.RunExact (k.cutProg g t) s
      (St ((amsterdamSteps s).feeBase b) [out / (17 : B256)] M G)
      (selected s k.shape.len.word g t) (.halted d))
    (next : Nonempty (Exec e s d ex)) :
    Nonempty (Exec 0 s (St b [] M (G + (amsterdamSteps s).feePathGas b n + dispatchGas)) ex) := by
  have path := feePath_exact (fs := k.cutProg g t) k.shape (amsterdamSteps_valid hfork) (revert := .undefined)
    (getter := g) (submission := t)
    ((congrArg (fun i => (k.cutProg g t)[i]?) hw).trans rfl)
    ((congrArg (fun i => (k.cutProg g t)[i]?) hl).trans rfl) off wordRun tail
  have root : SFunc.RunExact (k.cutProg g t) s (St b [] M (G + (amsterdamSteps s).feePathGas b n + dispatchGas))
      (k.cutRoot g t) (.halted d) :=
    dispatch_exact (by simpa only [dispatchArm, ite_eq_right caller] using path)
  exact exec_of_cut (es := es) (e := e) (by rw [hcode]; exact cutAll_spec cut.all) root rfl 0 none
    (by rw [hcode]; exact cut.root) (fun _ h => by cases h) next

end UserPath

/-- The count bump up to its `SSTORE`: `PUSH1 1; SLOAD; PUSH1 1; ADD; PUSH1 1`. -/
def countBumpCut : SFunc :=
  .next (.push [0x01] (by decide)) (.next (.reg .sload) (.next (.push [0x01] (by decide)) (.next (.reg .add)
    (.next (.push [0x01] (by decide)) (.last .stop)))))

/-- What the count bump's prefix takes from `gasLeft`, on the slot it reads. -/
def countBumpGas (s : Sevm) (b : Devm) : Nat := 3 + sloadCost s b 1 + 3 + 3 + 3

/-- The count bump, walked up to its `SSTORE`. -/
theorem countBump_exact {fs : List SFunc} {s : Sevm} {b : Devm} {M : Mem} {G : Nat}
    (hfork : s.benvStat.fork = .amsterdam) :
    SFunc.RunExact fs s (St b [] M (G + countBumpGas s b)) countBumpCut
      (.halted (St (afterSloadA s b 1) [1, 1 + b.getStorVal s.currentTarget 1] M G)) := by
  have hgas : G + countBumpGas s b = G + 3 + 3 + 3 + sloadCost s b 1 + 3 := by
    simp only [countBumpGas]
    omega
  rw [hgas]
  unfold countBumpCut
  refine rx_push rfl (by change 0 < 1024; decide) ?_
  refine rx_sloadA (amsterdam_access hfork) (by change 0 < 1024; decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  refine rx_add' rfl (by change 0 < 1024; decide) ?_
  refine rx_push rfl (by change 1 < 1024; decide) ?_
  exact .last rfl

theorem countBumpGas_le (s : Sevm) (b : Devm) : countBumpGas s b ≤ 12 + gasColdSload := by
  have := sloadCost_le s b 1
  unfold countBumpGas
  omega

end Blanc.Lift.BuilderRequest
