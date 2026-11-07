import Blanc.Lift.BuilderRequest.AmsterdamMsgProbeCall
import Blanc.Lift.NodeWalk
import Blanc.Reverts
import Blanc.Lift.FrameWalkCut

/-!
# Probe: a positive `REVERT` of certified bytes, at any storage

Disposable (goal `blanc-eip8282-builder-requests-v1`, O16). `Blanc/Lift/Exact.lean`'s node induction
returns only `.ok`: `Outcome` has no failing constructor. Short of editing that, the kit here checks a
straight segment against the bytes with `segEnd`, reuses the `rx_` walk on the segment cut with `STOP`,
and joins segments by hand at taken jumps. The kernel cannot do this alone: `SLOAD` tests a `HashSet`
of keys, and `mixHash` is opaque, so a closed `Evm.step` run stops at the first `SLOAD`.
-/

namespace Blanc.Lift.BuilderRequest.AmsterdamMsgProbe

open Jaune
open Blanc.Lift.NodeWalk (ninst_step_of_runCompiled)
open RequestSystem (dispatchTree dispatchGas dispatch_exact dispatchArm system_push)
open RequestFee (PushWord)

/-- The pc after a straight segment that ends in a cut `STOP`: instructions and fallen-through `JUMPI`s
at the bytes. `none` if the bytes disagree. -/
def segEnd (code : ByteArray) : Nat → SFunc → Option Nat
  | pc, .last .stop => some pc
  | pc, .next n f =>
    match code.getInst pc with
    | some (.next m) => if m = n ∧ nodeNoExec n = true then segEnd code (pc + n.size) f else none
    | _ => none
  | pc, .dest f =>
    match code.getInst pc with
    | some (.jump .jumpdest) => segEnd code (pc + 1) f
    | _ => none
  | pc, .branch f .undefined =>
    match code.getInst pc with
    | some (.jump .jumpi) => segEnd code (pc + 1) f
    | _ => none
  | _, _ => none

theorem exec_of_seg {s : Sevm} {ex : Execution} {fs : List SFunc} :
    ∀ (f : SFunc) {pc e : Nat} {d d' : Devm}, segEnd s.code pc f = some e →
      SFunc.RunExact fs s d f (.halted d') → Nonempty (Exec e s d' ex) →
      Nonempty (Exec pc s d ex)
  | .last l, pc, e, d, d', h, run, k => by
    cases l with
    | stop =>
      simp only [segEnd, Option.some.injEq] at h
      subst h
      cases run with
      | last hrun =>
        have hd : d = d' := by
          change Except.ok _ = Except.ok _ at hrun
          cases hrun
          rfl
        rw [hd]
        exact k
    | _ => simp only [segEnd, reduceCtorEq] at h
  | .next n f, pc, e, d, d', h, run, k => by
    simp only [segEnd] at h
    split at h
    · rename_i m hm
      split at h
      · rename_i hc
        obtain ⟨rfl, hn⟩ := hc
        cases run with
        | next hstep hrest =>
          obtain ⟨c⟩ := exec_of_seg f h hrest k
          have hat : Ninst.At s.code pc m := hm
          exact ⟨Exec.cont ((Evm.step_next hat).trans
            (ninst_step_of_runCompiled (nodeNe_of_noExec hn) hstep pc)) c⟩
      · simp only [reduceCtorEq] at h
    · simp only [reduceCtorEq] at h
  | .dest f, pc, e, d, d', h, run, k => by
    simp only [segEnd] at h
    split at h
    · rename_i hm
      cases run with
      | dest hb hrest =>
        obtain ⟨c⟩ := exec_of_seg f h hrest k
        have hat : Jinst.At s.code pc .jumpdest := hm
        exact ⟨Exec.cont (Evm.jumpdest_cont hat hb) c⟩
    · simp only [reduceCtorEq] at h
  | .branch f g, pc, e, d, d', h, run, k => by
    cases g with
    | undefined =>
      simp only [segEnd] at h
      split at h
      · rename_i hm
        cases run with
        | zero x hpop hrest =>
          obtain ⟨c⟩ := exec_of_seg f h hrest k
          have hat : Jinst.At s.code pc .jumpi := hm
          have hs := popBurnBy_two_stack' hpop
          have hg : gHigh ≤ d.gasLeft := by have := hpop.gasLeft; omega
          have hstep := Evm.jumpi_cont_zero hat hs hg
          rw [popBurnBy_setMach hpop] at hstep
          exact ⟨Exec.cont hstep c⟩
        | succ x w hne hpop hrest => cases hrest
      · simp only [reduceCtorEq] at h
    | _ => simp only [segEnd, reduceCtorEq] at h
  | .jump _, _, _, _, _, h, _, _ => by simp only [segEnd, reduceCtorEq] at h
  | .ret, _, _, _, _, h, _, _ => by simp only [segEnd, reduceCtorEq] at h
  | .branchTo _ _, _, _, _, _, h, _, _ => by simp only [segEnd, reduceCtorEq] at h
  | .callNext _ _, _, _, _, _, h, _, _ => by simp only [segEnd, reduceCtorEq] at h
  | .pcAt _ _, _, _, _, _, h, _, _ => by simp only [segEnd, reduceCtorEq] at h
  | .undefined, _, _, _, _, h, _, _ => by simp only [segEnd, reduceCtorEq] at h

/-- A `JUMPI` taken, between segments. -/
theorem exec_jumpi_taken {s : Sevm} {b : Devm} {S : List B256} {M : Mem} {G pc : Nat} {x w : B256}
    {ex : Execution} (hat : Jinst.At s.code pc .jumpi) (hw : w ≠ 0)
    (hj : jumpable s.code x.toNat = true) (k : Nonempty (Exec x.toNat s (St b S M G) ex)) :
    Nonempty (Exec pc s (St b (x :: w :: S) M (G + 10)) ex) := by
  obtain ⟨c⟩ := k
  have hstep := Evm.jumpi_cont_jump (devm := St b (x :: w :: S) M (G + 10)) (s := S) hat rfl hw
    (by show gHigh ≤ G + 10; have : gHigh = 10 := rfl; omega) hj
  have e : (St b (x :: w :: S) M (G + 10)).setMach ⟨S, M, G + 10 - gHigh, b.stateGas⟩ = St b S M G := by
    show _ = _
    rw [show G + 10 - gHigh = G from rfl]
    rfl
  rw [show (St b (x :: w :: S) M (G + 10)).memory = M from rfl,
    show (St b (x :: w :: S) M (G + 10)).gasLeft = G + 10 from rfl,
    show (St b (x :: w :: S) M (G + 10)).stateGas = b.stateGas from rfl, e] at hstep
  exact ⟨Exec.cont hstep c⟩

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

/-! ## The inhibited user path, generic in the code -/

/-- The bytes of the user path up to the inhibitor's taken `JUMPI`, and of its `REVERT` arm. -/
structure InhibitBytes (code : ByteArray) where
  sysDest : PushWord
  dest : PushWord
  jumpiAt : Nat
  revertAt : Nat
  seg1 : segEnd code 0 (dispatchTree sysDest
    (.next (.push [] (by decide)) (.next (.reg .sload) (.next (.reg (.dup 0))
    (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
      0xff, 0xff] (by decide)) (.next (.reg .eq)
    (.next (.push (dest.head :: dest.tail) dest.le) (.last .stop))))))) .undefined) = some jumpiAt
  jumpi : Jinst.At code jumpiAt .jumpi
  jumpable : Jaune.jumpable code dest.word.toNat = true
  seg2 : segEnd code dest.word.toNat
    (.dest (.next (.push [] (by decide)) (.next (.push [] (by decide)) (.last .stop)))) = some revertAt
  rev : Linst.At code revertAt .revert

/-- The inhibited frame's fixed charge, beside the `SLOAD`. -/
def inhibitFixed : Nat := dispatchGas + 2 + 3 + 3 + 3 + 3 + 10 + 1 + 2 + 2

/-- **While slot 0 holds the inhibitor, a non-system call executes `REVERT`.** Any calldata, value,
storage and memory; given the gas. Not only "does not succeed": the failure and its machine are named. -/
theorem exec_inhibited_reverts {code : ByteArray} (B : InhibitBytes code) {s : Sevm} {b : Devm} {M : Mem}
    {G : Nat} (hcode : s.code = code) (hacc : s.benvStat.rules.access = .eip2929)
    (hp0 : s.benvStat.rules.op.push0 = true) (caller : s.caller ≠ systemAddress)
    (inhibited : b.getStorVal s.currentTarget 0 = B256.max) :
    Nonempty (Exec 0 s (St b [] M (G + inhibitFixed + sloadCost s b 0))
      (.error (.revert, (St (afterSloadA s b 0) [B256.max] M G).withOutput []))) := by
  subst hcode
  have run2 : SFunc.RunExact [] s (St (afterSloadA s b 0) [B256.max] M (G + 1 + 2 + 2))
      (.dest (.next (.push [] (by decide)) (.next (.push [] (by decide)) (.last .stop))))
      (.halted (St (afterSloadA s b 0) [0, 0, B256.max] M G)) := by
    refine rx_dest ?_
    refine rx_push0 (h_push0 := hp0) (by change 1 < 1024; decide) ?_
    refine rx_push0 (h_push0 := hp0) (by change 2 < 1024; decide) ?_
    exact .last rfl
  have after := exec_of_seg _ B.seg2 run2 (exec_revert_empty (M := M) (G := G)
    (b := afterSloadA s b 0) (S := [B256.max]) B.rev)
  have taken := exec_jumpi_taken (x := B.dest.word) (w := 1) (S := [B256.max])
    (b := afterSloadA s b 0) (M := M) (G := G + 1 + 2 + 2) B.jumpi (by decide) B.jumpable after
  have run1 : SFunc.RunExact [] s (St b [] M (G + 1 + 2 + 2 + 10 + 3 + 3 + 3 + 3 + sloadCost s b 0 + 2 + dispatchGas))
      (dispatchTree B.sysDest
        (.next (.push [] (by decide)) (.next (.reg .sload) (.next (.reg (.dup 0))
        (.next (.push [0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
          0xff, 0xff] (by decide)) (.next (.reg .eq)
        (.next (.push (B.dest.head :: B.dest.tail) B.dest.le) (.last .stop))))))) .undefined)
      (.halted (St (afterSloadA s b 0) [B.dest.word, 1, B256.max] M (G + 1 + 2 + 2 + 10))) := by
    refine dispatch_exact ?_
    simp only [dispatchArm, ite_eq_right caller]
    refine rx_push0 (h_push0 := hp0) (by change 0 < 1024; decide) ?_
    refine rx_sloadV hacc (by change 0 < 1024; decide) inhibited ?_
    refine rx_dup1 (by change 1 < 1024; decide) ?_
    refine rx_push (w := B256.max) (by decide) (by change 2 < 1024; decide) ?_
    refine rx_eq (v := 1) (by decide) (by change 1 < 1024; decide) ?_
    refine rx_push rfl (by change 2 < 1024; decide) ?_
    exact .last rfl
  have hg : G + inhibitFixed + sloadCost s b 0 =
      G + 1 + 2 + 2 + 10 + 3 + 3 + 3 + 3 + sloadCost s b 0 + 2 + dispatchGas := by
    simp only [inhibitFixed, dispatchGas]
    omega
  rw [hg]
  exact exec_of_seg _ B.seg1 run1 taken

end Blanc.Lift.BuilderRequest.AmsterdamMsgProbe
