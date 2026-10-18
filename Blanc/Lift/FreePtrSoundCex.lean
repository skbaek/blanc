import Blanc.Lift.FreePtrSound

/-!
# A counterexample to the frozen `fpRun_sound` (evidence for the master, not for merging)

`fpNode`'s `callNext` arm accepts without checking the continuation when the callee's
declared frame holds no `.ret` slot (`findIdx? = none => true`).  That is sound only when
such a callee cannot return, which `Cert.check` guarantees (`checkNode`'s `.ret` arm needs an
abstract `.ret` on top) but `fpCert` alone does not: `fpNode`'s `.ret` arm ignores the
abstract stack.  `fpRun_sound` assumes `fpCert` only, so a two-entry certificate whose
callee (frame `[]`) pushes a word and returns, followed by an unchecked `PUSH 0x40; MLOAD`
on empty memory, is accepted and runs, yet its free-pointer read sees `0`.
-/

namespace Blanc.Lift.FreePtr.Cex

open Jaune AbstractStackSafety

def callee : SFunc := .next (.push [0] (by decide)) .ret
def cont : SFunc := .next (.push [0x40] (by decide)) (.next (.reg .mload) (.last .stop))
def main : SFunc := .next (.push [5] (by decide)) (.callNext 1 cont)
def cert : Cert := [(⟨0, [], 0⟩, main), (⟨5, [], 0⟩, callee)]
def ann : List Ann := [⟨FSt.init, FSt.init⟩, ⟨FSt.init, FSt.init⟩]

theorem cert_fp : fpCert cert ann = true := by decide

def pre : Devm := { (default : Devm) with mach := { (default : Devm).mach with gasLeft := 1000 } }

def outOf : Step → Devm
  | .cont _ d => d
  | _ => default

def popTop (d : Devm) : Devm := { d with mach := { d.mach with stack := d.mach.stack.tail } }

def d1 : Devm := outOf (Ninst.step ⟨0, default, pre⟩ (.push [5] (by decide)))
def d2 : Devm := popTop d1
def d3 : Devm := outOf (Ninst.step ⟨0, default, d2⟩ (.push [0] (by decide)))
def d4 : Devm := popTop d3
def d5 : Devm := outOf (Ninst.step ⟨0, default, d4⟩ (.push [0x40] (by decide)))
def d6 : Devm := outOf (Ninst.step ⟨0, default, d5⟩ (.reg .mload))
def post : Devm :=
  match Linst.run default d6 .stop with
  | .ok d => d
  | _ => default

theorem popTop_burn {d : Devm} {x : B256} (h : d.stack.head? = some x) :
    Devm.PopBurn [x] d (popTop d) := by
  obtain ⟨ys, hs⟩ : ∃ ys, d.mach.stack = x :: ys := by
    change d.mach.stack.head? = some x at h
    cases e : d.mach.stack with
    | nil => rw [e] at h; cases h
    | cons y ys => rw [e] at h; cases h; exact ⟨ys, rfl⟩
  refine ⟨?_, rfl, Nat.le_refl _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl⟩
  change d.mach.stack = [x] ++ (popTop d).mach.stack
  simp only [popTop, hs, List.tail_cons, List.singleton_append]

theorem pot {d : Devm} (h : d.gasMeasure + calculateMemoryGasCost d.memory.size < 2 ^ 256) :
    Pot d := h

/-- The step relation of the counterexample: Jaune's step with the potential recorded. -/
def P : Sevm → Devm → Ninst → Devm → Prop := fun s d n d' => Ninst.Run s d n d' ∧ Pot d ∧ Pot d'

theorem run_main : SProg.RunP P cert.prog default pre post := by
  refine ⟨main, rfl, ?_⟩
  refine .next ⟨⟨.none, trivial, 0, ⟨rfl, rfl⟩⟩, pot (by decide), pot (by decide)⟩ ?_
  refine .callRet (5 : B256) (g := callee) (devm'' := popTop d3) rfl (popTop_burn (d := d1) rfl) ?_ ?_
  · exact .next ⟨⟨.none, trivial, 0, ⟨rfl, rfl⟩⟩, pot (by decide), pot (by decide)⟩
      (.ret (0 : B256) (popTop_burn (d := d3) rfl))
  · refine .next ⟨⟨.none, trivial, 0, ⟨rfl, rfl⟩⟩, pot (by decide), pot (by decide)⟩ ?_
    refine .next ⟨⟨.none, trivial, 0, ⟨rfl, rfl⟩⟩, pot (by decide), pot (by decide)⟩ ?_
    exact .last rfl

theorem not_good_empty : ¬ FpGood (memWord Mem.empty 64) := by
  unfold FpGood fpLo
  decide

theorem memory_of_pop {xs : List B256} {d d' : Devm} (h : Devm.PopBurn xs d d') :
    d'.memory = d.memory := h.memory.symm

theorem no_fp_run : ¬ SProg.RunP (FpStep P) cert.prog default pre post := by
  rintro ⟨f, hf, run⟩
  cases hf
  cases run with
  | next h1 run =>
    cases run with
    | callHalt _ hg _ run =>
      cases hg
      cases run with
      | next _ run => cases run
    | callRet _ hg pop1 runC runK =>
      cases hg
      cases runC with
      | next h2 runC =>
        cases runC with
        | ret _ pop2 =>
          cases runK with
          | next h3 runK =>
            cases runK with
            | next h4 _ =>
              have p1 := of_run_push h1.1.1
              have p2 := of_run_push h2.1.1
              have p3 := of_run_push h3.1.1
              have hm : _ = pre.memory :=
                p3.memory.symm.trans ((memory_of_pop pop2).trans
                  (p2.memory.symm.trans ((memory_of_pop pop1).trans p1.memory.symm)))
              refine not_good_empty ?_
              have := h4.2 rfl (by
                have hs := p3.stack
                simp only [Stack.Push, Split] at hs
                rw [hs]
                rfl)
              rw [hm] at this
              exact this

/-- **The frozen `fpRun_sound` is false.** -/
theorem fpRun_sound_false :
    ¬ (∀ {P : Sevm → Devm → Ninst → Devm → Prop}
      (_ : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d' ∧ Pot d ∧ Pot d')
      {c : Cert} {ann : List Ann} (_ : fpCert c ann = true)
      {sevm : Sevm} (_ : CoveredFork sevm.benvStat.fork) {pre post : Devm}
      (_ : pre.memory = Mem.empty) (_ : SProg.RunP P c.prog sevm pre post),
      SProg.RunP (FpStep P) c.prog sevm pre post) :=
  fun h => no_fp_run (h (P := P) id cert_fp (sevm := default) (by decide) rfl run_main)

end Blanc.Lift.FreePtr.Cex
